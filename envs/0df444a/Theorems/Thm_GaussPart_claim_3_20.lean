-- Prove2me | Theorems.Thm_GaussPart_claim_3_20
-- name    : GaussPart.claim_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:06.75538+00:00
-- url     : https://prove2.me/theorems/97d91ae4-571d-46f3-985e-7b1905d26eb9
-- title:
--   Claim 3.20 — search over the reduced subspace (correctness and the net; the time bound is in Proposition 3.3)
-- statement:
--   Under the hypotheses of Proposition 3.3 ($d,k\ge1$, $\Delta\in(0,1/2)$, $V,H\ge1$, the $V$-assumption), with Algorithm 2's $\tau=\Delta/(100k2^kF_k)$ and $\rho=\Delta/(100kF_kH)$, on the estimation event and if the algorithm does not reject:
--   1. **(search)** for any ρ-net $\mathcal C$ of $W'\cap S^{d-1}$ and any $(\ell^*,w)$ maximizing $|\hat F_\ell(z)|$ over $\ell\in[k]$, $z\in\mathcal C$, where $\hat F_\ell(z)=\frac1n\sum_s(z\cdot x^{(s)})^\ell-\mathbb E[Z^\ell]$: if $|\hat F_{\ell^*}(w)|\ge\Delta/2$ then $|F_{\ell^*}(w)|\ge3\Delta/8$, and otherwise $|F_\ell(v)|<\Delta$ for every unit $v$ and every $\ell\in[k]$;
--   2. **(net)** the explicit grid net of the proof, carried to $W'$ by an orthonormal basis, is a ρ-net of $W'\cap S^{d-1}$ with at most
--   $$\exp\Big(C'k^{C'k}\frac{H^2}{\Delta^2}\log\frac H\Delta\Big)$$
--   points, for a universal constant $C'$.
--
--   Together with the $d^{O(k)}$ cost per net point, this gives the running time $d^{O(k)}\exp(O(k^{O(k)})(H^2/\Delta^2)\log(H/\Delta))$ of the search.
--
--   **Formalization Note** The search part is stated for every family of subspaces $U_i$ with $\|\mathrm{proj}_{U_i^\perp}\hat M_i\|_{op}\le\tau$ and every augmentation $W'$ of their sum; the net part for the exact singular subspaces. The time bound of the search is part of `GaussPart.proposition_3_3`, whose program performs it.
--
--   Differences from the source:
--   - encoding: E_{x∼Q}[p(x)²] ≤ V∥p∥²_{L²(P)} for every polynomial of degree ≤ k → PolyMomentBound Q V k: lower Lebesgue integrals of p², polynomials MvPolynomial (Fin d) ℝ of total degree ≤ k; reason: a Bochner integral of a non-integrable p² would be 0 and make the assumption vacuous
--   - generalization: the search over W′ built from the singular subspaces, with Algorithm 2's net → any subspaces U_i with ∥proj_{U_i^⊥} M̂_i∥_op ≤ τ, any augmentation W′, any ρ-net and any maximizer; reason: the proof uses only these properties; Algorithm 2's choices are instances
--   - reading: "a search … can be implemented in time d^{O(k)} exp(O(k^{O(k)})(H²/Δ²) log(H/Δ))" → the size bound of the explicit net here; the machine time bound in GaussPart.proposition_3_3; reason: a running time needs a machine; the finder program of Proposition 3.3 contains this search
--   - encoding: O(·) in the net size → one constant C′ > 0 chosen before all parameters; reason: uniform constant
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Claim 3.20, p.34 (PDF p.36), and its proof pp.34–35; Algorithm 2, lines 12–17, p.29

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_GaussPart_FinderObjects

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Claim 3.20** (Search over the Reduced Subspace), correctness of the search and size of the net.

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Claim 3.20, p.34 (PDF p.36), with its proof
(pp.34–35) and Algorithm 2, lines 12–17, p.29.

"On the estimation event, assuming that the algorithm does not reject, a search over W′ ∩ S^{d−1}
can be implemented in time d^{O(k)} exp(O(k^{O(k)}) (H²/∆²) log(H/∆)). It returns a direction with
discrepancy at least 3∆/8 in some degree, or certifies that all directional discrepancies in degrees
1, …, k are smaller than ∆."

**Formalization Note.**
* Standing hypotheses of Proposition 3.3 (`k, d ≥ 1`, `∆ ∈ (0, 1/2)`, `V, H ≥ 1`,
  `PolyMomentBound Q V k`), the sample `xs ∈ (ℝ^d)^n`, `n ≥ 1`, Algorithm 2's `τ = finderTau k ∆`
  and `ρ = finderRho k ∆ H`, the estimation event and no rejection, as in `claim_3_19`.
* **Search correctness** (first conjunct): for subspaces `U_i` with `∥proj_{U_i^⊥} M̂_i∥_op ≤ τ`
  (the singular subspaces are one such family), any augmentation `W′` of their sum, any `ρ`-net `C`
  of `W′ ∩ S^{d−1}`, and any maximizer `(ℓ*, w)` of `|F̂_ℓ(z)|` over `[k] × C` (`empiricalGap`): if
  `|F̂_{ℓ*}(w)| ≥ ∆/2` (a direction is returned) then `|F_{ℓ*}(w)| ≥ 3∆/8`; otherwise (None) every
  unit `v` and every `ℓ ∈ [k]` have `|F_ℓ(v)| < ∆`.
* **The net** (second conjunct): with the singular subspaces, for every orthonormal basis of `W′`,
  the image of the explicit grid net of p.34 (`gridNet`) is a `ρ`-net of `W′ ∩ S^{d−1}` with at most
  `exp(C′ k^{C′k} (H²/∆²) log(H/∆))` points, for one constant `C′` chosen first.
* The running time is part of `GaussPart.proposition_3_3`, whose machine performs this search. -/
theorem claim_3_20 :
    ∃ C' : ℝ, 0 < C' ∧
    ∀ {d : ℕ}, 1 ≤ d → ∀ (k : ℕ), 1 ≤ k → ∀ (Q : Measure (Vec d)) [IsProbabilityMeasure Q]
      (Δ V H : ℝ), 0 < Δ → Δ < 1 / 2 → 1 ≤ V → 1 ≤ H → PolyMomentBound Q V k →
      ∀ (n : ℕ), 1 ≤ n → ∀ (xs : Fin n → Vec d),
      (∀ i : ℕ, 1 ≤ i → i ≤ k →
        frobeniusNorm (fun J => empiricalTensor xs i J - hermiteMoment Q i J) ≤ finderTau k Δ) →
      (∀ i : ℕ, 1 ≤ i → i ≤ k → frobeniusNorm (empiricalTensor xs i) ≤ 2 * H) →
      (∀ U : Fin k → Submodule ℝ (Vec d),
        (∀ m : Fin k, OpBoundOn (U m) (empiricalTensor xs (m.val + 1)) (finderTau k Δ)) →
        ∀ W' : Submodule ℝ (Vec d), IsAugmented (⨆ m, U m) W' →
        ∀ C : Finset (Vec d), IsNet W' (finderRho k Δ H) C →
        ∀ (ℓs : ℕ) (w : Vec d), 1 ≤ ℓs → ℓs ≤ k → w ∈ C →
          (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → ∀ z ∈ C, |empiricalGap xs ℓ z| ≤ |empiricalGap xs ℓs w|) →
          (Δ / 2 ≤ |empiricalGap xs ℓs w| → 3 * Δ / 8 ≤ |momentGap Q ℓs w|) ∧
          (|empiricalGap xs ℓs w| < Δ / 2 →
            ∀ v : Vec d, ‖v‖ = 1 → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → |momentGap Q ℓ v| < Δ)) ∧
      (∀ W' : Submodule ℝ (Vec d),
        IsAugmented (⨆ m : Fin k, singularSubspace (empiricalTensor xs (m.val + 1))
          (finderTau k Δ)) W' →
        ∀ (r : ℕ) (b : OrthonormalBasis (Fin r) ℝ W'),
          IsNet W' (finderRho k Δ H)
              ((gridNet r (finderRho k Δ H)).image fun y => ((b.repr.symm y : W') : Vec d)) ∧
            (((gridNet r (finderRho k Δ H)).image
                fun y => ((b.repr.symm y : W') : Vec d)).card : ℝ) ≤
              Real.exp (C' * (k : ℝ) ^ (C' * k) * (H ^ 2 / Δ ^ 2) * Real.log (H / Δ))) := by sorry

end GaussPart
