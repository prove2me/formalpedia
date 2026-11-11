-- Prove2me | Theorems.Thm_OptQJunta_lemma_2_33
-- name    : OptQJunta.lemma_2_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:34.532466+00:00
-- url     : https://prove2.me/theorems/0b0c3f65-2e3a-4cb0-9e12-d8bd82729500
-- title:
--   Lemma 2.33 — label-preserving amplitude estimation with $O(\tau^{-1/2}\ln(1/\beta))$ queries
-- statement:
--   Let $A$ be a finite-dimensional unitary, let $\{\Pi_j\}_{j\in E}$ be a known family of orthogonal projectors indexed by a finite set $E$, and put $p_j=\|\Pi_jA|0\rangle\|^2$. For $0<\tau\le1$ and $0<\beta<1/2$ there is a unitary circuit $V$ that uses $O(\tau^{-1/2}\ln(1/\beta))$ ordinary queries to $A,A^\dagger$ in an order depending only on $\tau$ and $\beta$, and satisfies $V|j\rangle|0\rangle=|j\rangle|\xi_j\rangle$ for every $j\in E$ ($|0\rangle$ the all-zero state of the work registers). For each $j$, measuring the answer bit of $|\xi_j\rangle$ gives
--
--   $$
--   \text{SMALL if } p_j\le\tau/4,\qquad \text{LARGE if } p_j\ge\tau,
--   $$
--
--   with error at most $\beta$.
--
--   Precisely: an absolute constant $C$; the number of queries and the $A/A^\dagger$ pattern are fixed from $\tau,\beta$ alone; one circuit for all labels and all unitaries $A$; the output on $|0\rangle|j\rangle|0\rangle$ vanishes off label $j$.
--
--   It is the minimum-marginal and gap-test subroutine of Theorem 3.19.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a procedure that prepares states and measures $\Pi$ (or a circuit with an answer bit) → a `SamplerAlg`/`SamplerCirc` in unitary form whose output is read from the final computational-basis measurement; reason: deferred measurement; "some measurement succeeds" is the output `true`
--   - encoding: $A$ a finite-dimensional unitary, $|0\rangle$ its zero state → a unitary matrix on $\mathbb C^V$ for an arbitrary finite $V$, with zero state a given basis vector $v_0$; the work registers are label $E$, answer bit and a finite workspace with zero state $w_0$; reason: a choice of basis; the circuit applies $A$ or $A^\dagger$ to the $V$ register only
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 2.33, p.25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg

open QAlgorithms

namespace OptQJunta

/-- **Lemma 2.33** (Quantum amplitude estimation [BHMT02]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.25). Let `A` be a
finite-dimensional unitary, let `{Π_j}_{j∈E}` be a known family of orthogonal projectors indexed by a
finite set `E`, and put `p_j = ‖Π_j A|0⟩‖²`. For `0 < τ ≤ 1` and `0 < β < 1/2`, there is a unitary
circuit `V` that uses `O(τ^{−1/2} ln(1/β))` ordinary queries to `A, A†` in an order depending only on
`τ` and `β`, and that satisfies `V|j⟩|0⟩ = |j⟩|ξ_j⟩` for every `j ∈ E`, where `|0⟩` is the all-zero
state of the work registers. For each `j ∈ E`, measuring the answer bit of `|ξ_j⟩` gives SMALL if
`p_j ≤ τ/4` and LARGE if `p_j ≥ τ`, with error at most `β`.

**Formalization Note** The constant `C` is absolute. The number of queries `T` and the order
`dir` of the calls to `A`/`A†` are chosen from `τ`, `β` alone, before the space `V` of `A`, its zero
state `v₀`, the label set `E` and the projectors; the circuit (a `SamplerCirc` with that `dir`, acting
on `V × (E × Bool × W)`: `A`'s register, label, answer bit, work) may depend on those, and is one
circuit for all labels and all unitaries `A`. Its input is `|v₀⟩|j⟩|0⟩|w₀⟩`; the output vanishes off
label `j` (label preservation), and the answer bit (`true` = LARGE) errs with probability `≤ β`. -/
theorem lemma_2_33 :
    ∃ C : ℝ, 0 < C ∧ ∀ τ β : ℝ, 0 < τ → τ ≤ 1 → 0 < β → β < 1 / 2 →
      ∃ (T : ℕ) (dir : Fin T → Bool), (T : ℝ) ≤ C * τ ^ (-(1 : ℝ) / 2) * Real.log (1 / β) ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V] (v₀ : V) (E : Type) [Fintype E] [DecidableEq E]
          (P : E → Matrix V V ℂ), (∀ j, IsOrthProj (P j)) →
          ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (w₀ : W)
            (Cc : SamplerCirc V (E × Bool × W) T), Cc.dir = dir ∧
            ∀ (A : Matrix.unitaryGroup V ℂ) (j : E),
              (∀ z : V × (E × Bool × W), z.2.1 ≠ j →
                Cc.run (A : Matrix V V ℂ) (ket (v₀, (j, false, w₀))) z = 0) ∧
              (ampProb (P j) (A : Matrix V V ℂ) v₀ ≤ τ / 4 →
                probEvent (Cc.run (A : Matrix V V ℂ) (ket (v₀, (j, false, w₀))))
                  (fun z => z.2.2.1 = true) ≤ β) ∧
              (τ ≤ ampProb (P j) (A : Matrix V V ℂ) v₀ →
                probEvent (Cc.run (A : Matrix V V ℂ) (ket (v₀, (j, false, w₀))))
                  (fun z => z.2.2.1 = false) ≤ β) := by sorry

end OptQJunta
