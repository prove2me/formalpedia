-- Prove2me | Theorems.Thm_GeoSemialgCSP_proposition_5_3
-- name    : GeoSemialgCSP.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:23.674635+00:00
-- url     : https://prove2.me/theorems/eeb4bfac-a312-4505-be42-7db763381e4e
-- title:
--   Proposition 5.3 — soundness against pseudorandom solutions
-- statement:
--   Let $k\ge2$, let $P$ be the restriction to $X^k$ of a semialgebraic predicate $S$ on $(\mathbb R^d)^k$, and let $(X,P)$ have property (2). Let $\theta(x;y)$ (solution set $\Theta\subseteq\mathbb R^{d+p}$) be a semialgebraic formula with the partition property of Theorem 7.1 for $P$ (any constants $d_{\mathrm{fVC}}$, $K_P$), and let $\mathcal C=\{C(y)\cap X: y\in\mathbb R^p\}$ be the family of regions it supplies, restricted to $X$ (p.14); it is fixed before the solution and the partition accuracy are chosen. Then the following holds. Fix $\eta\in(0,1)$ and $\gamma>0$; there is $q_0$ (from Lemma 5.2) such that for all $\varepsilon,\varepsilon_L>0$, every height $h\ge1$ with the property of Lemma 4.1 for $q_0$ and $\varepsilon$, and every random map $L_{m,M}$ with items 1–3 of Lemma 4.2 for error $\varepsilon_L$, there is $\tau>0$, independent of $R$, such that every fractional solution $\xi$ (output points in $X$) satisfies
--   $$\mathrm{val}(\xi,(D_R)_P)\ \le\ \alpha^*_P+\varepsilon+\gamma$$
--
--   1. whenever $T_{1-\eta}\xi$ is $\tau$-pseudorandom with respect to $\mathcal C$, and
--   2. in particular, whenever $\xi$ is $\tau$-pseudorandom with respect to $\mathcal C$.
--
--   This is the soundness of the dictatorship test, used in the Unique Games reduction.
--
--   Differences from the source:
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - generalization: property (2): a cousins homomorphism for every finite ordered k-ary tree → HasCousinsHoms: one for every complete ordered k-ary tree; reason: a weaker hypothesis: every finite ordered k-ary tree embeds in a complete one preserving cousins tuples, so the printed property implies it; the proof uses only complete trees (Lemma 4.3 item 4)
--   - generalization: C = the fixed family of regions supplied by Theorem 7.1 (its formula θ), restricted to X (p.14) → C = {C(y) ∩ X : y ∈ ℝ^p} for every semialgebraic Θ ⊆ ℝ^{d+p} with Theorem 7.1's property (PartitionFormula S dfVC KP Θ), given as hypotheses before η; reason: Theorem 7.1's θ is existential, so the page's C is the family of one such Θ; the statement for every such Θ specializes to it, and the proof uses only Theorem 7.1's property of θ and (V2)
--   - reading: choose q₀ by Lemma 5.2, the height by Lemma 4.1 with error ε, M and L_{m,M} by Lemma 4.2 with error ε_L → ∃ q₀ depending on P, η, γ; then every h ≥ 1 with the Lemma 4.1 property for q₀, ε and every L with items 1–3 at ε_L; reason: the paper's choices are any objects with these properties; the Lean quantifies over all of them
--   - encoding: a fractional solution ξ : [M]^R → finitely supported distributions on X → points x : Fin n → E d in X and G : [M]^R → P_n; reason: the paper's own description (p.12): all distributions live on one finite set {x₁, …, x_n}
--   - generalization: R ≥ 1 (Let R ≥ 1, p.11) → every R : ℕ; reason: the R ≥ 1 cases are included; at R = 0 the test has a single variable and the inequality also holds
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Proposition 5.3, p.15 (PDF p.16); the region family C, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_HasCousinsHoms
import Definitions.Def_GeoSemialgCSP_MSSound
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3
import Definitions.Def_GeoSemialgCSP_valD
import Definitions.Def_GeoSemialgCSP_fS
import Definitions.Def_GeoSemialgCSP_noiseOpV
import Definitions.Def_GeoSemialgCSP_alphaStar
import Definitions.Def_GeoSemialgCSP_RegPR
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
import Definitions.Def_GeoSemialgCSP_PartitionFormula

namespace GeoSemialgCSP

/-- **Proposition 5.3 (soundness against pseudorandom solutions).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Proposition 5.3, printed
p.15 (PDF p.16): fix `η ∈ (0,1)` and `ε, γ, ε_L > 0`; choose the partition accuracy and `q₀` by
Lemma 5.2, the multiscale height by Lemma 4.1 with error `ε`, and `M, L_{m,M}` by Lemma 4.2 with
error `ε_L`. There is `τ > 0`, independent of `R`, such that every fractional solution `ξ`
satisfies `val(ξ, (D_R)_P) ≤ α*_P + ε + γ` whenever `T_{1−η}ξ` is `τ`-pseudorandom; in particular
whenever `ξ` is `τ`-pseudorandom.

**Formalization Note.** Pseudorandomness is with respect to the region family `C` of §5, "the
fixed family of regions supplied by the semialgebraic partition theorem, Theorem 7.1, restricted
to X" (p.14): for a semialgebraic formula `Θ ⊆ ℝ^{d+p}` with Theorem 7.1's property
(`PartitionFormula S dfVC KP Θ`), `C` is the family of traces `C(y) ∩ X`, `y ∈ ℝ^p`. The statement
holds for **every** such `Θ` (whichever one Theorem 7.1 supplies), so `C` is fixed before `η`.
`q₀` depends only on `P, η, γ` and `Θ`'s constants (Lemma 5.2), the height is any `h ≥ 1`
satisfying Lemma 4.1 for `q₀` and `ε`, and `L` any map with items 1–3 of Lemma 4.2. -/
theorem proposition_5_3 {k d : ℕ} (hk : 2 ≤ k) (X : Set (E d)) (S : Set (Fin k → E d))
    (hsa : IsSemialgebraicPred S) (hcous : HasCousinsHoms X S)
    (p : ℕ) (Θ : Set (Fin (d + p) → ℝ)) (hΘ : NonconvexSplitting.ADMMKL.IsSemialgebraicSet Θ)
    (dfVC : ℕ) (KP : ℝ) (hpart : PartitionFormula S dfVC KP Θ) :
    let C : Set (Set (E d)) :=
      Set.range (fun y : Fin p → ℝ => {z : E d | z ∈ X ∧ Fin.append (fun i => z i) y ∈ Θ})
    ∀ η : ℝ, 0 < η → η < 1 → ∀ γ : ℝ, 0 < γ → ∃ q₀ : ℕ,
      ∀ ε εL : ℝ, 0 < ε → 0 < εL → ∀ h : ℕ, 1 ≤ h → MSSound k q₀ ε h →
      ∀ (H : ℕ) (L : PMF ((Fin h → Fin k) → Wd k H)), RE1 L → RE2 L → RE3 L εL →
      ∃ τ : ℝ, 0 < τ ∧ ∀ (R n : ℕ) (x : Fin n → E d) (G : (Fin R → Wd k H) → Fin n → ℝ),
        (∀ i, x i ∈ X) → (∀ z, G z ∈ stdSimplex ℝ (Fin n)) →
        (RegPR C τ x (noiseOpV (1 - η) G) → valD L R η (fS S x) G ≤ alphaStar X S + ε + γ) ∧
        (RegPR C τ x G → valD L R η (fS S x) G ≤ alphaStar X S + ε + γ) := by sorry

end GeoSemialgCSP
