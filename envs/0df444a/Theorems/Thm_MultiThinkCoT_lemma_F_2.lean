-- Prove2me | Theorems.Thm_MultiThinkCoT_lemma_F_2
-- name    : MultiThinkCoT.lemma_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:54.192973+00:00
-- url     : https://prove2.me/theorems/2f4cdfaf-a8d7-4ec6-a04a-415a99bb374e
-- title:
--   Lemma F.2 — each $\hat f_k$ is a weak learner for $D^{(k)}$, with $M_\star=O(\mathrm{VCdim})$
-- statement:
--   There are a universal constant $c>0$ and budget functions $\mathrm{Mst},\mathrm{Mst}':\mathbb N\to\mathbb N$ with $\mathrm{Mst}(v)\le cv$ and $\mathrm{Mst}'(w)\le cw$ such that the following hold.
--
--   1. **Strict protocol.** Fix $\mathcal F$, $T$, $\mathcal X$ with $\mathrm{VCdim}(\mathcal F^{\mathrm{e2e}\text{-}T})=v<\infty$, a target $h^\star\in\mathcal F^{\mathrm{e2e}\text{-}T}$, and a training set $x^{(1)},\dots,x^{(m)}\in\mathcal X$ ($m\ge1$) with labels $y^{(i)}=h^\star(x^{(i)})$. Fix also any $K$, any $\delta\in(0,1)$, any Consistent oracle and any strict adversary for $h^\star$. Algorithm 1 run with $M_\star=\mathrm{Mst}(v)$ then satisfies, with probability at least $1-\delta/2$ over its internal randomness of subsampling, for every executed round $k$
--   $$
--   \epsilon_k=\Pr_{i\sim D^{(k)}}\big[\hat f_k^{\mathrm{e2e}\text{-}T}(x^{(i)})\neq h^\star(x^{(i)})\big]\le0.25 .
--   $$
--   2. **Relaxed protocol.** The same holds against relaxed adversaries (the source $f_{k,\ell}$ fixed before $S_{k,\ell}$ is seen) with $M_\star=\mathrm{Mst}'(w)$, where $w=\mathrm{VCdim}(\mathcal L^{\mathrm{CoT}\text{-}T}(\mathcal F))<\infty$.
--   3. **Relaxed budget.** $\mathrm{Mst}'(w)\le c\,p\,\max\{1,\log T\}$ whenever $\mathrm{VCdim}(\mathcal F)$ over $\mathcal X\times\{0,1\}^{\le T-1}$ is $p$.
--
--   This is the weak-learning step: with this budget every boosting round produces a predictor of weighted error at most $1/4$, whatever sources the adversary picks.
--
--   **Formalization Note** The budgets depend on the VC dimension alone and are fixed before the class, the training set, $K$ and $\delta$. The event "for all $k\in[K]$" ranges over the rounds the run executes (rounds after an early return at line 14 do not exist). The adversary sees the inputs, the history and, in the strict protocol, the current subset. $m\ge1$ because line 1 divides by $m$. Natural logarithms.
--
--   Differences from the source:
--   - generalization: for a fixed training set and δ, there exists a choice of M⋆ ≤ c VCdim(F^{e2e-T}) → budget functions Mst, Mst' of the VC dimension alone, with Mst v ≤ c v, chosen before F, T, X, the training set, K and δ; reason: a uniform choice is in particular a choice for each training set and δ; it is the order Theorem 7 needs (M⋆ independent of ε)
--   - reading: for all k ∈ [K] simultaneously, ϵ_k ≤ 0.25 → every executed outer round of the run has ϵ_k ≤ 0.25 (the recorded errors); reason: after a line-14 return no further rounds exist
--   - encoding: ϵ_k = Pr_{x∼D(k)}[f̂_k^{e2e-T}(x) ≠ h⋆(x)] → Σ_i D(k)_i 1[f̂_k^{e2e-T}(x(i)) ≠ y(i)] with y(i) = h⋆(x(i)); reason: line 7's formula; the two agree on a training set labelled by h⋆
--   - encoding: the training set S_e2e (m unspecified) → 1 ≤ m; reason: Algorithm 1, line 1 sets D(1) = (1/m, …, 1/m), undefined at m = 0
--   - encoding: the adversary chooses f_{k,ℓ} from the history and S_{k,ℓ} (or the history alone) → deterministic strategies, ∀-quantified, that also see the inputs x(1..m); reason: a randomized adversary is a mixture of deterministic ones
--   - encoding: M⋆ ≤ c VCdim(L^{CoT-T}(F)) = O(VCdim(F) log T) → Mst' w ≤ c w, and Mst' w ≤ c p max{1, log T} when VCdim(L^{CoT-T}(F)) = w and VCdim(F) over X × {0,1}^{≤T−1} is p; reason: O(·) with a universal constant and max{1, log} for logarithmic factors (p.16)
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, Lemma F.2, p.54 (PDF p.54)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_e2eClass
import Definitions.Def_MultiThinkCoT_cotLossClass
import Definitions.Def_MultiThinkCoT_prefixClass
import Definitions.Def_MultiThinkCoT_alg1

namespace MultiThinkCoT

/-- **Lemma F.2 (`f̂_k` are weak learners for `D⁽ᵏ⁾`)**, p.54 (PDF p.54).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a universal `c > 0` and a choice of the per-source budget `M⋆ ≤ c VCdim(F^{e2e-T})` such
that, for any fixed training set `S_e2e = {(x(i), y(i))}` labelled by a target `h⋆ ∈ F^{e2e-T}`,
any `K` and any `δ ∈ (0,1)`, Algorithm 1 run with this `M⋆` satisfies, with probability at least
`1 − δ/2` over its internal randomness of subsampling, `ϵ_k ≤ 0.25` for all `k ∈ [K]`
simultaneously. In the relaxed protocol (the source `f_{k,ℓ}` is fixed before `S_{k,ℓ}` is
observed) the same guarantee holds with `M⋆ ≤ c VCdim(L^{CoT-T}(F)) = O(VCdim(F) log T)`.

**Formalization Note.**
* The budget is a function `Mst` (resp. `Mst'`) of the VC dimension alone, chosen before `F`,
  `T`, `X`, the training set and `δ` (stronger than the printed order, which fixes the training
  set and `δ` first).
* "`ϵ_k ≤ 0.25` for all `k ∈ [K]`" is the event that every executed outer round has
  `ϵ_k ≤ 0.25` (`Outcome.errs`); rounds after a line-14 return are not executed. Its complement
  is bounded by `δ/2`.
* The oracle meets `IsConsistentOracle F`; the adversary is any strict (resp. relaxed) strategy for
  `h⋆` (Definition 2.3; p.25), seeing the inputs, the history and (strict only) the current
  subset. The cost functions are arbitrary.
* `= O(VCdim(F) log T)` is the conjunct `Mst'(w) ≤ c p max{1, log T}` whenever
  `VCdim(L^{CoT-T}(F)) = w` and `VCdim(F)` over `X × {0,1}^{≤T−1}` is `p`.
* `1 ≤ m`: line 1 divides by `m`.
-/
theorem lemma_F_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ Mst Mst' : ℕ → ℕ,
      (∀ v, (Mst v : ℝ) ≤ c * v) ∧ (∀ w, (Mst' w : ℝ) ≤ c * w) ∧
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (w p : ℕ),
        UnderstandingML.vcDim (cotLossClass F T X) = w →
        UnderstandingML.vcDim (prefixClass F T X) = p →
        (Mst' w : ℝ) ≤ c * p * max 1 (Real.log T)) ∧
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (v : ℕ),
        UnderstandingML.vcDim (e2eClass F T X) = v →
        ∀ hstar ∈ e2eClass F T X, ∀ m : ℕ, 1 ≤ m → ∀ xs : Fin m → X,
        ∀ (K : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ),
          IsConsistentOracle F O →
        ∀ A : (Fin m → X) → History m → Finset (Fin m) → Gen,
          IsStrictAdversary F T X hstar A →
        (alg1 T O oc ec K (Mst v) δ (fun i => (xs i).1) (fun i => hstar (xs i)) (A xs)).toOuterMeasure
            {r | ∃ e ∈ r.errs, 1 / 4 < e} ≤ ENNReal.ofReal (δ / 2)) ∧
      (∀ (F : Set Gen) (T : ℕ) (X : Set (List Bool)) (w : ℕ),
        UnderstandingML.vcDim (cotLossClass F T X) = w →
        ∀ hstar ∈ e2eClass F T X, ∀ m : ℕ, 1 ≤ m → ∀ xs : Fin m → X,
        ∀ (K : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ),
          IsConsistentOracle F O →
        ∀ R : (Fin m → X) → History m → Gen,
          IsRelaxedAdversary F T X hstar R →
        (alg1 T O oc ec K (Mst' w) δ (fun i => (xs i).1) (fun i => hstar (xs i))
            (fun hist _ => R xs hist)).toOuterMeasure
            {r | ∃ e ∈ r.errs, 1 / 4 < e} ≤ ENNReal.ofReal (δ / 2)) := by sorry

end MultiThinkCoT
