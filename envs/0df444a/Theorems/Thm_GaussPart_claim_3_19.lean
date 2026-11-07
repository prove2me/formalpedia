-- Prove2me | Theorems.Thm_GaussPart_claim_3_19
-- name    : GaussPart.claim_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:04.549607+00:00
-- url     : https://prove2.me/theorems/eff2bdec-7ff1-4a24-a5f5-92bc10b95db6
-- title:
--   Claim 3.19 — reduction to a low-dimensional subspace
-- statement:
--   Under the hypotheses of Proposition 3.3 ($d,k\ge1$, $V,H\ge1$, the $V$-assumption), let $\tau\in(0,1)$ and let a sample satisfy the estimation event $\|\hat A_i-A_i\|_F\le\tau$ and the no-reject condition $\|\hat A_i\|_F\le2H$ for all $i\in[k]$. Let $U_i$ be the span of the left singular vectors of the flattening of $\hat A_i$ with singular value at least $\tau$, $W=U_1+\dots+U_k$, and $W'=W$ if $W=\mathbb R^d$, else $W'=W+\mathrm{span}\{e\}$ for a unit $e\perp W$. Then
--   $$\dim W'\le1+\frac{4kH^2}{\tau^2},$$
--   and for every unit $u$ there is a unit $\bar u\in W'$ with, for every $\ell\in[k]$, $|F_\ell(\bar u)-F_\ell(u)|\le4F_k2^k\tau$, and in particular $|F_\ell(\bar u)|\ge|F_\ell(u)|-4F_k2^k\tau$, where $F_\ell(z)=\mathbb E_Q[(z\cdot x)^\ell]-\mathbb E_P[(z\cdot x)^\ell]$ and $F_k=(2k)^{2k}$.
--
--   This is why the finder only needs to search a subspace of dimension independent of $d$.
--
--   **Formalization Note** The dimension bound is stated for the exact singular subspaces. The representative bound is stated for every family of subspaces $U_i$ with $\|\mathrm{proj}_{U_i^\perp}\hat M_i\|_{op}\le\tau$ (`OpBoundOn`), which includes the singular subspaces.
--
--   Differences from the source:
--   - encoding: E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial of degree ≤ k → PolyMomentBound Q V k: lower Lebesgue integrals of p², polynomials MvPolynomial (Fin d) ℝ of total degree ≤ k; reason: a Bochner integral of a non-integrable p² would be 0 and make the assumption vacuous
--   - generalization: U_i = span of the left singular vectors of M̂_i with singular value ≥ τ (representative clause) → any subspaces U_i with ∥proj_{U_i^⊥} M̂_i∥_op ≤ τ; reason: the proof (p.33) uses only this bound; the singular subspaces satisfy it
--   - encoding: on the estimation event, assuming that the algorithm does not reject → hypotheses ∥Â_i − A_i∥_F ≤ τ and ∥Â_i∥_F ≤ 2H for every i ∈ [k], for a sample of size n ≥ 1; reason: the two conditions as defined on pp.31–32
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Claim 3.19, p.32 (PDF p.34); Algorithm 2, lines 9–11, p.29

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Claim 3.19** (Low-dimensional Reduction).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Claim 3.19, p.32 (PDF p.34), in the proof of
Proposition 3.3; Algorithm 2, lines 9–11, p.29.

"On the estimation event, assuming that the algorithm does not reject, dim(W′) ≤ 1 + 4kH²/τ².
Moreover, for every u ∈ S^{d−1} there exists a unit vector ū ∈ W′ such that, simultaneously for
every ℓ ∈ [k], |F_ℓ(ū) − F_ℓ(u)| ≤ 4F_k 2^k τ. In particular, |F_ℓ(ū)| ≥ |F_ℓ(u)| − 4F_k 2^k τ."

**Formalization Note.**
* Standing hypotheses of Proposition 3.3 (`k, d ≥ 1`, `V, H ≥ 1`, `PolyMomentBound Q V k`) and
  `τ ∈ (0, 1)`. The sample is `xs ∈ (ℝ^d)^n`, `n ≥ 1`; `Â_i = empiricalTensor xs i`,
  `A_i = hermiteMoment Q i`. The estimation event is `∥Â_i − A_i∥_F ≤ τ` and "does not reject" is
  `∥Â_i∥_F ≤ 2H`, for every `i ∈ [k]`. `F_ℓ` is `momentGap Q ℓ` and `F_k = (2k)^{2k}`.
* `U_i` is `singularSubspace Â_i τ` (eigenvalues of `M̂_i M̂_iᵀ` at least `τ²`), `W` their sum, and
  `W′` any augmentation of `W` (`IsAugmented`: `W′ = W` if `W = ℝ^d`, else `W + span{e}` for a unit
  `e ⊥ W`). The dimension clause is stated for these `U_i`.
* The representative clause is stated for every family of subspaces `U_i` with
  `∥proj_{U_i^⊥} M̂_i∥_op ≤ τ` (`OpBoundOn`), which the singular subspaces satisfy; the proof uses only
  this property. Index `m < k` stands for `i = m + 1`. -/
theorem claim_3_19 {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (Q : Measure (Vec d))
    [IsProbabilityMeasure Q] (V H : ℝ) (hV : 1 ≤ V) (hH : 1 ≤ H) (hQ : PolyMomentBound Q V k)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (n : ℕ) (hn : 1 ≤ n) (xs : Fin n → Vec d)
    (hest : ∀ i : ℕ, 1 ≤ i → i ≤ k →
      frobeniusNorm (fun J => empiricalTensor xs i J - hermiteMoment Q i J) ≤ τ)
    (hnorej : ∀ i : ℕ, 1 ≤ i → i ≤ k → frobeniusNorm (empiricalTensor xs i) ≤ 2 * H) :
    (∀ W' : Submodule ℝ (Vec d),
      IsAugmented (⨆ m : Fin k, singularSubspace (empiricalTensor xs (m.val + 1)) τ) W' →
        (Module.finrank ℝ W' : ℝ) ≤ 1 + 4 * k * H ^ 2 / τ ^ 2) ∧
    (∀ U : Fin k → Submodule ℝ (Vec d),
      (∀ m : Fin k, OpBoundOn (U m) (empiricalTensor xs (m.val + 1)) τ) →
      ∀ W' : Submodule ℝ (Vec d), IsAugmented (⨆ m, U m) W' →
      ∀ u : Vec d, ‖u‖ = 1 → ∃ ub ∈ W', ‖ub‖ = 1 ∧
        ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k →
          |momentGap Q ℓ ub - momentGap Q ℓ u| ≤ 4 * finderF k * 2 ^ k * τ ∧
          |momentGap Q ℓ u| - 4 * finderF k * 2 ^ k * τ ≤ |momentGap Q ℓ ub|) := by sorry

end GaussPart
