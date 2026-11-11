-- Prove2me | Theorems.Thm_HamLocality237_Testing_distance_from_locality
-- name    : HamLocality237.Testing.distance_from_locality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:56.685994+00:00
-- url     : https://prove2.me/theorems/f4872ef7-f5c5-4d8c-b672-35af69362119
-- title:
--   §2.2 — distance from locality and diagonal Fourier formulas
-- statement:
--   Let $n\ge1$, let $0\le k\le n$, and let $H$ be a Hermitian $n$-qubit operator. Write $H_{\le k}$ and $H_{>k}$ for its Pauli truncations. For every $k$-local $L$,
--
--   $$\|H-L\|_2^2=\|H_{>k}\|_2^2+\|H_{\le k}-L\|_2^2.$$
--
--   The low-weight truncation is itself $k$-local and attains the distance. In particular,
--
--   $$\operatorname{dist}(H,k\text{-local})=\|H-H_{\le k}\|_2=\|H_{>k}\|_2,\qquad
--   \operatorname{dist}(H,k\text{-local})^2=\sum_{|P|>k}|\widehat H(P)|^2.$$
--
--   If $H=\operatorname{diag}(h_x)$ for a real table $h$, both diagonal identities hold:
--
--   $$\operatorname{dist}(H,k\text{-local})^2=\sum_{|S|>k}|\widehat h(S)|^2
--   =2^{-n}\sum_x|h_x|^2-\sum_{|S|\le k}|\widehat h(S)|^2.$$
--
--   This gives the attained best approximation and the Fourier expression needed for the farness argument. It adds no operator-norm or trace-zero hypothesis.
--
--   Differences from the source:
--   - encoding: sites indexed by [n] and sums over Pauli words and subsets → sites indexed by Fin n, finite conditional sums, and complex coefficient norms; reason: wire j represents source wire j+1; these enumerate exactly the same words and subsets and give the same absolute squares
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §2.2, pp.8–9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Locality

open QAlgorithms
open scoped BigOperators

namespace HamLocality237.Testing

/-- §2.2, pp.8--9: Pythagoras, a closest truncation, both diagonal formulas. -/
theorem distance_from_locality (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (H : Operator n) (hH : H.IsHermitian) :
    (∀ L : Operator n, IsKLocal k L →
      normalizedFrobenius (H - L) ^ 2 = normalizedFrobenius (highWeight k H) ^ 2 +
        normalizedFrobenius (lowWeight k H - L) ^ 2) ∧
    IsKLocal k (lowWeight k H) ∧
    distanceFromLocality k H = normalizedFrobenius (H - lowWeight k H) ∧
    distanceFromLocality k H = normalizedFrobenius (highWeight k H) ∧
    distanceFromLocality k H ^ 2 =
      (∑ P : PauliWord n, if k < QAlgorithms.opsWeight P then ‖pauliCoefficient H P‖ ^ 2 else 0) ∧
    (∀ h : Qubits n → ℝ, H = diagonalHamiltonian h →
      distanceFromLocality k H ^ 2 =
        ∑ S : Finset (Fin n), if k < S.card then |booleanCoefficient h S| ^ 2 else 0) ∧
    (∀ h : Qubits n → ℝ, H = diagonalHamiltonian h →
      distanceFromLocality k H ^ 2 =
        ((2 : ℝ) ^ n)⁻¹ * (∑ x : Qubits n, |h x| ^ 2) -
          (∑ S : Finset (Fin n), if S.card ≤ k then |booleanCoefficient h S| ^ 2 else 0)) := by sorry

end HamLocality237.Testing
