-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_11
-- name    : GMMIsoSample.Main.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:11.081199+00:00
-- url     : https://prove2.me/theorems/34da2050-ed94-4706-b76d-7e3c8d404be4
-- title:
--   Lemma 11 — ClusterMoreSamplePoints extends the exact clustering to M fresh points, w.p. ≥ 98/100
-- statement:
--   Let ExactClustering be as in Theorem 4 (amplification constant $A$, polynomial $P$, both existentially quantified). Consider the regime of Proposition 10: $k_{\max}=2$, $0<w_{\min}\le1/2$, or $k_{\max}>2$, $0<w_{\min}\le1/3$; $0<\varepsilon\le1/100$; $\delta=1/100$; and any constant $C_{CMS}>0$ in (15)/(16). For all sufficiently large $d$, if $\Gamma_0=\min\{\Gamma_{\min},d^{1/4}\}$ is above a polylogarithmic threshold $c_0(\log d)^{a_0}$, then for every target $D$ with $\Gamma(D)\ge\Gamma_{\min}$, every $M_0\in\{N_{CMS,2},N_{CMS,k_{\max}}\}$ and $M$ the smallest multiple of $N_{EC}/2$ that is at least $M_0$, the following holds with probability at least
--   $$\frac{98}{100}$$
--   over an i.i.d. sample $S$ of size $N_{EC}$, an independent i.i.d. sample $X$ of size $M$ and the algorithms' randomness: ExactClustering$(k_{\max},w_{\min},\Gamma_0,S)$ returns $S_1\sqcup\dots\sqcup S_k$, and ClusterMoreSamplePoints$(X,S_1,\dots,S_k)$ returns $S'_1\sqcup\dots\sqcup S'_k$ which is the correct clustering of $S\cup X$ with $k$ the true number of components and $S_i\subseteq S'_i$ — for every output either algorithm can produce.
--
--   This bootstraps exact clustering, which is guaranteed only at sample size $N_{EC}$, to the larger samples the hypothesis-construction step needs.
--
--   Differences from the source:
--
--   - reading: ExactClustering and NEC of Theorem 4 (with the undefined CountClusters) → ∃ A > 0 and a polynomial P, as in Theorem 4; reason: the lemma refers to Theorem 4's algorithm and sample size; finding I1
--   - generalization: M0 = NCMS,2 or NCMS,kmax with the constants C_wmin, C_{kmax,wmin} of Lemmas 12–13 → every constant C_CMS > 0 in (15) and (16); reason: the source's constants are particular positive values, so the statement specializes to them
--   - reading: 'Γmin above the exact-clustering threshold so that Γ0 lies in the key range (5)' → c₀ (log d)^{a₀} ≤ min{Γmin, d^{1/4}} for some c₀ > 0, a₀ ≥ 0 depending on kmax, wmin, ε, C_CMS; reason: the polylog threshold of Theorem 4 (Γ0 ≤ d^{1/4} holds by definition of Γ0)
--   - reading: ExactClustering run on H ⊔ T_ℓ → on the anchor points in the order of π₁ followed by the batch points in the order of π₂; reason: the paper does not fix the order of the batch; CountClusters reads points in input order
--   - encoding: S (size NEC) and an independent X (size M) → one i.i.d. labelled sample of size NEC + M, S its first NEC entries and X the rest; reason: the same joint law
--   - encoding: output S'_1 ⊔ ⋯ ⊔ S'_k → a map sending each reference block S_i to S'_i; correctness: k blocks, their images are exactly the true classes, all components present, S_i ⊆ S'_i; reason: keeps the correspondence S_i ↦ S'_i the conclusion speaks about
--   - encoding: uniformly random subsets / pairings / partitions chosen by the algorithm → read off one uniformly random permutation of the indices (average over all permutations); reason: consecutive runs of a uniformly permuted list are uniformly random disjoint subsets and a uniformly random pairing / partition
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 15, Lemma 11 (proof pp. 19–20; Figure 2, p. 19)

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 11 (p. 15), with ExactClustering as in Theorem 4 (amplification constant `A`,
polynomial `P`): in the regime of Proposition 10 (`kmax = 2, wmin ≤ 1/2` or `kmax > 2,
wmin ≤ 1/3`; `0 < ε ≤ 1/100`), for every constant `C_CMS > 0` in (15)/(16) and all sufficiently
large `d`, if `Γ₀ = min{Γmin, d^{1/4}}` is above the polylogarithmic threshold, then for every
target `D` with `Γ(D) ≥ Γmin`, `M₀ ∈ {N_CMS,2, N_CMS,kmax}` and `M` the smallest multiple of
`NEC/2` that is at least `M₀`: with probability at least `98/100` over an i.i.d. sample `S` of
size `NEC`, an independent i.i.d. sample `X` of size `M` and the algorithm's uniform random
permutations, ExactClustering succeeds on `S` and ClusterMoreSamplePoints(X, S₁, …, S_k) returns
extensions `S'_i ⊇ S_i` forming the correct clustering of `S ∪ X` with `k` the true number of
components — for every output either algorithm can produce. -/
theorem lemma_11 :
    ∃ A : ℝ, 0 < A ∧ ∃ P : MvPolynomial (Fin 2) ℝ, ∀ (kmax : ℕ) (wmin : ℝ),
      ((kmax = 2 ∧ 0 < wmin ∧ wmin ≤ 1 / 2) ∨ (2 < kmax ∧ 0 < wmin ∧ wmin ≤ 1 / 3)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ Ccms : ℝ, 0 < Ccms →
      ∃ c₀ a₀ : ℝ, 0 < c₀ ∧ 0 ≤ a₀ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ,
        c₀ * Real.log d ^ a₀ ≤ min Γmin ((d : ℝ) ^ (1 / 4 : ℝ)) →
        ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γmin p →
        ∀ M₀ : ℝ, (M₀ = nCMS2 Ccms ε d Γmin ∨ M₀ = nCMSk Ccms ε d kmax) →
          let Γ₀ : ℝ := min Γmin ((d : ℝ) ^ (1 / 4 : ℝ))
          let n : ℕ := nEC (MvPolynomial.eval ![(kmax : ℝ), 1 / wmin] P) d Γ₀
          let M : ℕ := (n / 2) * ⌈M₀ / ((n / 2 : ℕ) : ℝ)⌉₊
          avgPerm n (fun π₁ => avgPerm M (fun π₂ =>
            iidLaw (labeledMix p) (n + M)
              {x | none ∈ exactClusteringOutputs A kmax wmin Γ₀
                    (fun t : Fin n => (x (Fin.castAdd M t)).2) ∨
                  ∃ blocks, some blocks ∈ exactClusteringOutputs A kmax wmin Γ₀
                      (fun t : Fin n => (x (Fin.castAdd M t)).2) ∧
                    ∃ o ∈ clusterMoreOutputs A kmax wmin Γ₀ (fun t => (x t).2) blocks π₁ π₂,
                      ¬ ClusterMoreCorrect blocks (fun t => (x t).1) o})) ≤ 2 / 100 := by sorry

end GMMIsoSample.Main
