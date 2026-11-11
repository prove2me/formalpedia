-- Prove2me | Theorems.Thm_OptQJunta_lemma_2_31
-- name    : OptQJunta.lemma_2_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:28.356208+00:00
-- url     : https://prove2.me/theorems/b25d2e14-bb99-4b5e-9d27-2091b92116ae
-- title:
--   Lemma 2.31 — amplitude amplification with $O(\zeta^{-1/2}\ln(1/\beta))$ queries and one-sided error
-- statement:
--   Let $A$ be a finite-dimensional unitary, let $\Pi$ be a known orthogonal projector, and put $p=\|\Pi A|0\rangle\|^2$. For $0<\zeta\le1$ and $0<\beta<1/2$ there is a procedure that prepares states, measures $\Pi$ on them, and uses $O(\zeta^{-1/2}\ln(1/\beta))$ ordinary queries to $A,A^\dagger$ on every input, such that
--
--   $$
--   p\ge\zeta\ \Rightarrow\ \Pr[\text{some measurement succeeds}]\ge1-\beta,\qquad p=0\ \Rightarrow\ \text{no measurement succeeds}.
--   $$
--
--   The constant is absolute; the procedure may depend on the space of $A$, its zero state and $\Pi$, and works for every unitary $A$. It is the $h=0$ test in the recovery branch of Theorem 4.2.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a procedure that prepares states and measures $\Pi$ (or a circuit with an answer bit) → a `SamplerAlg`/`SamplerCirc` in unitary form whose output is read from the final computational-basis measurement; reason: deferred measurement; "some measurement succeeds" is the output `true`
--   - encoding: $A$ a finite-dimensional unitary, $|0\rangle$ its zero state → a unitary matrix on $\mathbb C^V$ for an arbitrary finite $V$, zero state a given basis vector $v_0$; reason: a choice of basis
--   - encoding: ordinary queries to $A,A^\dagger$, each call's choice unrestricted → the procedure calls $A$ or $A^\dagger$ in a pattern fixed in advance (`SamplerCirc.dir`); reason: an adaptive choice between $A$ and $A^\dagger$ is simulated by the alternating pattern at twice the cost, so the query bound changes by a constant factor only; the fixed pattern only restricts the procedure the statement asserts to exist
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 2.31, p.24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg

open QAlgorithms

namespace OptQJunta

/-- **Lemma 2.31** (Quantum amplitude amplification [BHMT02]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.24). Let `A` be a
finite-dimensional unitary, let `Π` be a known orthogonal projector, and put `p = ‖Π A|0⟩‖²`. For
`0 < ζ ≤ 1` and `0 < β < 1/2`, there is a procedure that prepares states, measures `Π` on them, and
uses `O(ζ^{−1/2} ln(1/β))` ordinary queries to `A, A†` on every input. If `p ≥ ζ`, some measurement
succeeds with probability at least `1 − β`. If `p = 0`, no measurement succeeds.

**Formalization Note** The constant `C` is absolute. The procedure is a `SamplerAlg` on `A`'s space
`V` (zero state `v₀`) and a finite workspace, chosen after `V`, `v₀`, `Π` and before `A`; in unitary
form (deferred measurement) "some measurement succeeds" is the output `true`, so the two clauses are
`Pr[true] ≥ 1 − β` when `p ≥ ζ` and `Pr[true] = 0` when `p = 0`. -/
theorem lemma_2_31 :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ β : ℝ, 0 < ζ → ζ ≤ 1 → 0 < β → β < 1 / 2 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (v₀ : V) (P : Matrix V V ℂ), IsOrthProj P →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ) (M : SamplerAlg V W T)
          (out : V × W → Bool), (T : ℝ) ≤ C * ζ ^ (-(1 : ℝ) / 2) * Real.log (1 / β) ∧
          ∀ A : Matrix.unitaryGroup V ℂ,
            (ζ ≤ ampProb P (A : Matrix V V ℂ) v₀ →
                1 - β ≤ M.outputProb (A : Matrix V V ℂ) out true) ∧
              (ampProb P (A : Matrix V V ℂ) v₀ = 0 →
                M.outputProb (A : Matrix V V ℂ) out true = 0) := by sorry

end OptQJunta
