-- Prove2me | Theorems.Thm_FuchsVdGraaf_theorem_1
-- name    : FuchsVdGraaf.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:15.722543+00:00
-- url     : https://prove2.me/theorems/8b7e57b8-4be8-4154-ac58-a6064069978c
-- title:
--   Theorem 1 (corrected: (45)/(48) read $\sqrt{1-B^2}$) — quantum inequalities between $\mathrm{PE}$, $K$, $B$, $\mathrm{SD}$ and $\tfrac12\mathrm{Tr}|\rho_0-\rho_1|$
-- statement:
--   Let $\rho_0, \rho_1$ be density matrices of any finite size $N$. Write $\mathrm{PE}$, $K$, $B$, $\mathrm{SD}$ for the quantum probability of error, Kolmogorov distance, Bhattacharyya coefficient and Shannon distinguishability of $(\rho_0,\rho_1)$ (each optimised over all POVMs with any number of outcomes), $T = \mathrm{Tr}|\rho_0 - \rho_1|$ for the trace norm of the difference, and $H_2$ for the binary entropy in bits. Then all of the following hold.
--
--   1. (43), quantum: $\;1 - B \le K \le \sqrt{1 - B^2}$.
--   2. (44), quantum: $\;1 - H_2(\mathrm{PE}) \le \mathrm{SD} \le 1 - 2\,\mathrm{PE}$.
--   3. (45), quantum, which is (48): $\;1 - B \le \mathrm{SD} \le 1 - H_2\big(\tfrac12 - \tfrac12\sqrt{1 - B^2}\big)$.
--   4. (46): $\;1 - B \le \tfrac12 T \le \sqrt{1 - B^2}$.
--   5. (47): $\;1 - H_2\big(\tfrac12 - \tfrac14 T\big) \le \mathrm{SD} \le \tfrac12 T$.
--
--   In display form, the equivalent statement of the paper is
--
--   $$
--   \begin{aligned}
--   1 - B(\rho_0,\rho_1) &\le \tfrac12\mathrm{Tr}|\rho_0-\rho_1| \le \sqrt{1 - B(\rho_0,\rho_1)^2},\\
--   1 - H_2\big(\tfrac12 - \tfrac14\mathrm{Tr}|\rho_0-\rho_1|\big) &\le \mathrm{SD}(\rho_0,\rho_1) \le \tfrac12\mathrm{Tr}|\rho_0-\rho_1|,\\
--   1 - B(\rho_0,\rho_1) &\le \mathrm{SD}(\rho_0,\rho_1) \le 1 - H_2\Big(\tfrac12 - \tfrac12\sqrt{1 - B(\rho_0,\rho_1)^2}\Big).
--   \end{aligned}
--   $$
--
--   This is the main result of Fuchs and van de Graaf. The quantum Shannon distinguishability (the accessible information of two equiprobable states) has no closed formula, while the trace distance and the Bhattacharyya coefficient (the fidelity) do; these inequalities bound it on both sides, and they show that exponential indistinguishability is the same notion for all four measures.
--
--   The printed (48) (and (45)) has $\sqrt{1 - B}$ in place of $\sqrt{1 - B^2}$. That form is false: for $\rho_0 = |0\rangle\langle0|$ and $\rho_1 = |{+}\rangle\langle{+}|$, the Helstrom measurement gives $\mathrm{SD}(\rho_0,\rho_1) \ge 0.3991\ldots$, while every POVM has $B(p_0(E),p_1(E)) \ge |\langle 0|{+}\rangle| = 1/\sqrt2$, so the printed right side is at most $0.2230\ldots$. With the square the bound is $0.3991\ldots$, attained here.
--
--   Differences from the source:
--   - reading: $\min_{E\in\mathcal M}$, $\max_{E\in\mathcal M}$ in the quantum measures → infimum / supremum over the set of values at all POVMs; reason: the paper's own "more carefully, one should use infimum" (p.10); attainment is not part of Theorem 1.
--   - encoding: POVMs $\langle E_1,\dots,E_m\rangle$ and $\mathrm{Tr}(\rho E_x)$ → `E : Fin m → Matrix n n ℂ` for every `m : ℕ` and the real part of the trace; reason: Lean convention, covers every finite POVM.
--   - encoding: $H_2$ and $\mathrm{SD} = I(T;X)$ with base-2 logarithms → `WildeQIT.binaryEntropy` and `shannonDist` through the expansion (32), `Real.logb 2`; reason: the paper's own expansion, same values.
--   - encoding: (45) with quantum operands and (48) → stated once; reason: they are the same formula.
--   - correction: printed (48) (and (45)) "$1 - H_2(\tfrac12 - \tfrac12\sqrt{1 - B(\rho_0,\rho_1)})$" → $1 - H_2(\tfrac12 - \tfrac12\sqrt{1 - B(\rho_0,\rho_1)^2})$; reason: the printed form fails for $\rho_0 = |0\rangle\langle0|$, $\rho_1 = |{+}\rangle\langle{+}|$ ($\mathrm{SD} \ge 0.3991 > 0.2230$); the proof's line (72) and (46) have the square.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Theorem 1, eqs. (46)-(48) and Proposition 5, eqs. (43)-(45), p.17; proof p.20

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_FuchsVdGraaf_qErrorProb
import Definitions.Def_FuchsVdGraaf_qKolmogorov
import Definitions.Def_FuchsVdGraaf_qBhattacharyya
import Definitions.Def_FuchsVdGraaf_qShannonDist

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, **Theorem 1**, eqs. (46)–(48), p.17 (the
main result): Proposition 5 holds with the quantum measures `PE`, `K`, `B`, `SD` and density
matrices `ρ₀`, `ρ₁` as operands, and, equivalently, with `T = Tr|ρ₀ − ρ₁|`,

* (43) quantum: `1 − B ≤ K ≤ √(1 − B²)`;
* (44) quantum: `1 − H₂(PE) ≤ SD ≤ 1 − 2 PE`;
* (45) quantum = (48): `1 − B ≤ SD ≤ 1 − H₂(½ − ½ √(1 − B²))`;
* (46): `1 − B ≤ ½ T ≤ √(1 − B²)`;
* (47): `1 − H₂(½ − ¼ T) ≤ SD ≤ ½ T`.

(45) with quantum operands and (48) are the same formula, stated once.

**Correction.** The printed (48) (and (45)) reads `√(1 − B(ρ₀, ρ₁))` without the square. The
proof of Proposition 5 ends at (72), p.19, with the square, (46) carries it, and the printed form
is false: for `ρ₀ = |0⟩⟨0|`, `ρ₁ = |+⟩⟨+|`, the Helstrom measurement gives `SD ≥ 0.3991…`, while
`B ≥ |⟨0|+⟩| = 1/√2` makes the printed right side at most `0.2230…`.

**Formalization Note.** `PE`, `K`, `B`, `SD` are `qErrorProb`, `qKolmogorov`, `qBhattacharyya`,
`qShannonDist`: infima / suprema (the paper's min / max, p.10) over all POVMs with any finite number
of outcomes. `H₂` is `WildeQIT.binaryEntropy` (bits), `Tr|·|` is `WildeQIT.traceNorm`. Density
matrices are `WildeQIT.IsDensityOperator` matrices over an arbitrary finite index type. -/
theorem theorem_1 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    -- (43), quantum operands
    (1 - qBhattacharyya ρ0 ρ1 ≤ qKolmogorov ρ0 ρ1 ∧
      qKolmogorov ρ0 ρ1 ≤ Real.sqrt (1 - qBhattacharyya ρ0 ρ1 ^ 2)) ∧
    -- (44), quantum operands
    (1 - WildeQIT.binaryEntropy (qErrorProb ρ0 ρ1) ≤ qShannonDist ρ0 ρ1 ∧
      qShannonDist ρ0 ρ1 ≤ 1 - 2 * qErrorProb ρ0 ρ1) ∧
    -- (45), quantum operands, = (48) (corrected: `√(1 − B²)`)
    (1 - qBhattacharyya ρ0 ρ1 ≤ qShannonDist ρ0 ρ1 ∧
      qShannonDist ρ0 ρ1 ≤
        1 - WildeQIT.binaryEntropy (1 / 2 - 1 / 2 * Real.sqrt (1 - qBhattacharyya ρ0 ρ1 ^ 2))) ∧
    -- (46)
    (1 - qBhattacharyya ρ0 ρ1 ≤ 1 / 2 * WildeQIT.traceNorm (ρ0 - ρ1) ∧
      1 / 2 * WildeQIT.traceNorm (ρ0 - ρ1) ≤ Real.sqrt (1 - qBhattacharyya ρ0 ρ1 ^ 2)) ∧
    -- (47)
    (1 - WildeQIT.binaryEntropy (1 / 2 - 1 / 4 * WildeQIT.traceNorm (ρ0 - ρ1)) ≤
        qShannonDist ρ0 ρ1 ∧
      qShannonDist ρ0 ρ1 ≤ 1 / 2 * WildeQIT.traceNorm (ρ0 - ρ1)) := by sorry

end FuchsVdGraaf
