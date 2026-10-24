-- Prove2me | Theorems.Thm_OAI_Problem355_AuxiliaryZeroCount_weighted_count_le_log
-- name    : OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:17:23.5528+00:00
-- url     : https://prove2.me/theorems/3aa7d2a5-6077-4d06-9d11-62e738d5fb19
-- title:
--   Weighted count of singular lattice matrices with distinct projected columns is O(N⁶/I² · log N) (OpenAI Heilbronn triangle)
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
--   **Row data.** A `ZeroDeterminantCount.RowData` $D$ consists of a prime $B$, exponents $b, e, k$ with $e \le k$, a sublattice $L \subseteq \mathbb Z^3$ of index $I = B^{b+e}$ (`RowData.I`) containing $B^e\mathbb Z^3$, and an integer matrix $C$ with rows in $L$ whose reduction mod $B^k$ equals $P \cdot \mathrm{diag}(1, B^b, B^e) \cdot Q$ for invertible $P, Q$ over $\mathbb Z/B^k$. Put $h = B^k$ (`RowData.h`) and $E = B^e$ (`RowData.E`).
--
--   **The statement.** Let $D$ be row data, $q$ a prime with $E$ a unit mod $q$ and $h^{26} \le q$, $N \ge 1$, and $\mathcal L$ an auxiliary law for $q$ with $H = (B^k)^2$. Let $S$ be a finite set of integer matrices $A$ with:
--   - $\det A = 0$;
--   - every row of $A$ in $L$;
--   - $A_{2i} \neq 0$ for every column $i$;
--   - the three columns projecting to three distinct plane points;
--   - all entries bounded by $|A_{ij}| \le 2N$.
--
--   Then, with the absolute constant $K$ = `AuxiliaryZeroCount.countConstant`,
--   $$\sum_{A \in S} \mathrm{auxiliaryWeight}\bigl(A \bmod q\bigr) \;\le\; K\,\frac{N^6}{I^2}\,\frac{\log(4N)}{\log 2}.$$
--
--   Lean: `OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log`, OpenAI's theorem of that name (in `lean/OAI/Geometry/HeilbronnTriangle/AuxiliaryZeroCount.lean`).
-- source:
--   OpenAI, A power improvement in the Heilbronn triangle lower bound, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 191; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/HeilbronnTriangle/AuxiliaryZeroCount.lean (declaration OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log)

import Mathlib
import Definitions.Def_OAIQWHT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.AuxiliaryZeroCount

open Matrix PrimitiveNormal ZeroDeterminantCount LiftingProbability
open scoped BigOperators

theorem weighted_count_le_log
    (D : RowData) (q N : ℕ) [Fact q.Prime]
    (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
    (hparam : D.h ^ 26 ≤ (q : ℝ))
    (L : AuxiliarySampling.Law q ((D.B ^ D.k) ^ 2))
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hdet : ∀ A ∈ S, A.det = 0)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
    (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ)) :
    (∑ A ∈ S, auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2 *
        (Real.log (4 * (N : ℝ)) / Real.log 2) := by
  sorry

end Problem355.AuxiliaryZeroCount

end

end OAI
end
