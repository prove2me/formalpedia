-- Prove2me | Theorems.Thm_MFOTLMon_Monitor_theorem_3_9
-- name    : MFOTLMon.Monitor.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:07.64808+00:00
-- url     : https://prove2.me/theorems/fac81f2e-d04b-4d89-9be0-b629ec18751d
-- title:
--   Theorem 3.9, p. 15:16 — M_Φ outputs exactly the regular violation set (¬Φ)^(D̄,τ̄,i) whenever it executes line 9, and reaches every time point
-- statement:
--   Let $(\bar{\mathcal D},\bar\tau)$ be a temporal structure with domain $\mathbb N$, natural-number time stamps that are monotone and make progress, whose structures $\mathcal D_i$ are automatic with respect to one fixed constant domain representation $(\mathcal L,\nu)$ of $\mathbb N$, and which has a binary predicate $\prec$ interpreted as $<$ (the restrictions of §3.1). Let $\Phi$ be a bounded MFOTL formula in which every temporal subformula occurs once and the two direct subformulas of every $\mathsf S_I$ and $\mathsf U_I$ subformula have the same free variables. Then the monitoring algorithm $\mathsf M_\Phi$ of Fig. 2 has the following properties.
--
--   1. Whenever $\mathsf M_\Phi$ executes line 9 with counter value $i$, the output set $O$ and time stamp satisfy
--   $$O=(\neg\Phi)^{(\bar{\mathcal D},\bar\tau,i)},\qquad O\text{ is regular},\qquad\text{the time stamp output is }\tau_i.$$
--   2. For each $n\in\mathbb N$, $\mathsf M_\Phi$ eventually sets the counter $i$ to $n$.
--
--   So the monitor reports, for every time point and with no omission, exactly the tuples violating $\Phi$, i.e. the violations of $\square\Phi$, as regular sets over the fixed representation.
--
--   **Formalization Note.** The monitor is the state machine `run D Φ k` (state on entering the $(k+1)$st iteration); its output log holds every $(i,O,\tau_i)$ emitted by line 9 during the first $k$ iterations, so "whenever line 9 is executed" ranges over all entries of all logs. The monitor computes only from its store and never consults the semantics. Part (2) records the line-11 increment to $n>0$ by the preceding output at index $n-1$; $n=0$ is the initial value (line 2). A single iteration can advance the counter several times, so loop-entry values alone would omit intermediate values. "Effectively computable" in part (1) is a claim about automata constructions and is not formalized. The two conditions on $\Phi$ besides boundedness are the paper's "without loss of generality" assumptions (§3.4, §3.6). The repaired until construction (R1, R2) is used.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:16, Theorem 3.9 and Fig. 2 (p. 15:15)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

/-- Theorem 3.9 (p. 15:16). Let `(D̄, τ̄)` be a temporal structure with domain `ℕ` whose structures are
automatic with the common domain representation `rep` and interpret a binary `≺ ∈ R` as `<`, and let
`Φ` be bounded (each temporal subformula occurring once; the direct subformulas of each `S_I`, `U_I`
having the same free variables). The monitor `M_Φ` (Fig. 2) satisfies:
(i) whenever it executes line 9, the output set is regular and equal to `(¬Φ)^{(D̄,τ̄,i)}` (and the
output time stamp is `τᵢ`);
(ii) for each `n ∈ ℕ`, `M_Φ` eventually sets the counter `i` to `n`. For `n > 0`, the
line-11 increment is recorded by the output at index `n - 1`; `n = 0` is the initial value. -/
theorem theorem_3_9 {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (huniq : TemporalSubformulasOnce Φ) (hfree : DirectFreeAligned Φ) :
    (∀ (k n : ℕ) (O : Set (List ℕ)) (t : ℕ), (n, O, t) ∈ (run D Φ k).out →
        O = satSet D (Formula.neg Φ) n ∧ RegularRel rep (freeList Φ).length O ∧ t = D.τ n) ∧
    (∀ n : ℕ, n = 0 ∨ ∃ (k : ℕ) (O : Set (List ℕ)) (t : ℕ),
      (n - 1, O, t) ∈ (run D Φ k).out) := by sorry

end MFOTLMon.Monitor
