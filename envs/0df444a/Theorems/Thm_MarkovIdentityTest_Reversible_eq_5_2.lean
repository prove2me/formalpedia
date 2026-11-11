-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_eq_5_2
-- name    : MarkovIdentityTest.Reversible.eq_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:33.231802+00:00
-- url     : https://prove2.me/theorems/95305db3-7007-4855-a663-e2fecf09d7b9
-- title:
--   §5.2.3 Eq. (5.2) — retained quadratic row scores: mean in $[0,\ell n]$, second moment $\le 6\ell^2n(n-1)$
-- statement:
--   Let $Q$ be stochastic, $T$ an independent positive geometric time of mean $M\ge1$ and $x$ any initial state. Let $b_{ij}\ge0$ be row weights with $Q_{ij}b_{ij}\le\ell$ for all $i,j$, and let $D_i$ be the retained destination-count vector of row $i$ at time $T$, with total $L_i$. Then $S=\sum_{i:L_i\ge1}U_{b_i}(Q_i;D_i)/L_i$ and $S^2$ are integrable and
--   $$0\le\mathbb ES\le\ell n,\qquad\mathbb ES^2\le6\ell^2n(n-1).$$
--   The mean need not be $0$ because the retained destinations have the return-biased law $r_i$, not $Q_i$.
--
--   Differences from the source:
--
--   - encoding: a row distribution q_i → q_i = Q_i, the generating row; reason: the features √b_ij(1{y = j} − q_i(j)) must be centred under the generating row; this is how the paper uses (5.2)
--   - encoding: E at the geometric time → series over t with absolute convergence asserted; M ∈ ℝ, M ≥ 1; reason: same law
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 28, §5.2.3, Eq. (5.2)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- §5.2.3, Eq. (5.2) (Jia, p. 28 / PDF 30): with row weights `bᵢⱼ ≥ 0` and `qᵢ(j) bᵢⱼ ≤ ℓ`
(`qᵢ = Qᵢ`), the retained quadratic row scores `S = ∑_{i : Lᵢ ≥ 1} U_{bᵢ}(qᵢ; Dᵢ)/Lᵢ` at the
geometric time satisfy `0 ≤ E S ≤ ℓn` and `E S² ≤ 6ℓ²n(n-1)`. -/
theorem eq_5_2 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsStochastic Q) (M : ℝ)
    (hM : 1 ≤ M) (x : Fin n) (b : Matrix (Fin n) (Fin n) ℝ) (hb : ∀ i j, 0 ≤ b i j) (ℓ : ℝ)
    (hbℓ : ∀ i j, Q i j * b i j ≤ ℓ) :
    GeomIntegrable M Q x (fun _ ω => retainedQuadScore b Q ω) ∧
      0 ≤ geomExp M Q x (fun _ ω => retainedQuadScore b Q ω) ∧
      geomExp M Q x (fun _ ω => retainedQuadScore b Q ω) ≤ ℓ * n ∧
      GeomIntegrable M Q x (fun _ ω => retainedQuadScore b Q ω ^ 2) ∧
      geomExp M Q x (fun _ ω => retainedQuadScore b Q ω ^ 2) ≤ 6 * ℓ ^ 2 * n * (n - 1) := by sorry

end MarkovIdentityTest.Reversible
