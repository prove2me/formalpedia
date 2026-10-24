-- Prove2me | Theorems.Thm_OAI_Problem355_UniformFixedFiberCount_matrix_fiber_le
-- name    : OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:17:21.586773+00:00
-- url     : https://prove2.me/theorems/1fa594ee-d2b3-4c74-9fe9-684271b9d15c
-- title:
--   Uniform weighted count of orbit matrices in a fixed determinant fiber is O(log² N · N⁶/(BᵇBᵉ)²) (OpenAI Heilbronn triangle)
-- statement:
--   **Notation** (definitions bundle `OAIQWHT000` of this split). Integer $3 \times 3$ matrices are `IntMatrix`; column $j$ of $A$ projects to the plane point $(A_{0j}/A_{2j},\ A_{1j}/A_{2j})$ (`PlaneRowTransport.projectedColumn`).
--
--   An auxiliary law `AuxiliarySampling.Law q H`, for a prime $q$, is a finite probability space of outcomes $\omega$ with weights $w(\omega) \ge 0$ summing to $1$, each carrying a set $V_\omega \subseteq \mathbb F_q^3$ of a common size $s > 0$. Every $V_\omega$:
--   - avoids $0$ and has no three collinear points (`AuxiliaryCap.IsCap`);
--   - has no nontrivial relation $\sum_i x_i p_i = 0$ among three distinct points with integer coefficients $|x_i| \le H$.
--
--   The law also satisfies $q^2 \le 2000^3 H^6 s$ and the three weight bounds recorded in the structure. For three vectors $p_0, p_1, p_2 \in \mathbb F_q^3$, the auxiliary weight (`LiftingProbability.auxiliaryWeight q s w V p`) is
--   $$(q^3/s)^3 \cdot \sum_\omega w(\omega)\,[p_0, p_1, p_2 \in V_\omega],$$
--   the normalized probability that all three lie in the random set. For an integer matrix $A$, it is evaluated at the columns of $A$ reduced mod $q$.
--
--   **Prime-power data.** For a prime $B$, an exponent $k$ and a matrix $C$ over $\mathbb Z/B^k$, a `PrimePowerData B k C` records exponents $b \le e \le k$ and invertible matrices $P, Q$ with $C = P \cdot \mathrm{diag}(1, B^b, B^e) \cdot Q$. The $\mathrm{SL}_3$-orbit of $C$ (`Section04Orbit.slOrbit C`) is $\{gC : g \in \mathrm{SL}_3(\mathbb Z/B^k)\}$. A column $u$ is in the box of size $N$ (`Homogeneous.InBox N u`) when $0 \le u_0 < N$, $0 \le u_1 < N$ and $N \le u_2 < 2N$.
--
--   **The statement.** Let $B$ be a prime, $k \ge 0$, $q$ a prime coprime to $B^k$ with $(B^k)^{26} \le q$, $C$ a matrix over $\mathbb Z/B^k$ with prime-power data $(b, e, P, Q)$, $\mathcal L$ an auxiliary law for $q$ with $H = (B^k)^2$, and $N \ge 1$. Let $S$ be a finite set of integer matrices $A$ with:
--   - the reduction of $A$ mod $B^k$ in the $\mathrm{SL}_3$-orbit of $C$;
--   - every column of $A$ in the box of size $N$;
--   - the three columns projecting to three distinct plane points.
--
--   Then for every integer $t$ with $|t| < q$, with the absolute constant $K$ = `UniformFixedFiberCount.countConstant`,
--   $$\sum_{A \in S,\ \det A = t} \mathrm{auxiliaryWeight}\bigl(A \bmod q\bigr) \;\le\; K\,\frac{\log(2N)^2\, N^6}{(B^b B^e)^2}.$$
--   This is a uniform bound for the weighted count of matrices in one determinant fiber.
--
--   Lean: `OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le`, OpenAI's theorem of that name (in `lean/OAI/Geometry/HeilbronnTriangle/UniformFixedFiberCount.lean`).
-- source:
--   OpenAI, A power improvement in the Heilbronn triangle lower bound, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 191; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/HeilbronnTriangle/UniformFixedFiberCount.lean (declaration OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le)

import Mathlib
import Definitions.Def_OAIQWHT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.UniformFixedFiberCount

open Finset

theorem matrix_fiber_le
    {B k q : ℕ} (hB : B.Prime) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (L : AuxiliarySampling.Law q ((B ^ k) ^ 2))
    (hcop : (B ^ k).Coprime q) (hparam : ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (S : Finset NonzeroWeightedCount.IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      PlaneRowTransport.projectedColumn A i ≠ PlaneRowTransport.projectedColumn A j)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ S.filter (fun A => A.det = t),
      LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
        (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  sorry

end Problem355.UniformFixedFiberCount

end

end OAI
end
