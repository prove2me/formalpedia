-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_Supplement_serial_fixing_barrier
-- name    : InvariantMoneySecurity.Decomposition.Supplement.serial_fixing_barrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:35:24.042029+00:00
-- url     : https://prove2.me/theorems/c5054e09-bf56-42f5-aefa-6c0d23f8fd20
-- title:
--   Theorem 6.9 — barrier for serial-fixing reductions
-- statement:
--   Let $(X,S,I)$ be an invariant money scheme that satisfies the preparation assumption (Assumption 6.1): every quantum polynomial-time algorithm that receives $(p,x)\leftarrow M_n$ outputs a register of negligible expected accepted weight. Fix any workspace width $e(n)$, and for each serial number $p'$ let $\mathrm{Syn}_{p'}$ be a unitary on one $n$-qubit register with $\mathrm{Syn}_{p'}|0\rangle=|\$_{p'}\rangle$. Let $F^*$ be the adversary implemented by
--   $$U^*:=\sum_{p'}|p'\rangle\langle p'|\otimes\Big(\Pi_1^{(p')}\otimes\mathrm{Syn}_{p'}+\big(I-\Pi_1^{(p')}\big)\otimes I\Big)$$
--   on its serial-number register, its challenge register and a second output register, where $\Pi_1^{(p')}$ projects onto the span of all orbit states with serial number $p'$. Then:
--
--   1. $U^*$ is an adversary unitary (unitary and block diagonal in the serial number);
--   2. $F^*$ wins the game of Definition 2.4 with probability $1$: $\mathrm{win}_{F^*}(n)=1$ for every $n$;
--   3. for every serial-fixing reduction $R$,
--   $$\mathbb E_{(p,x)\leftarrow M_n}\big[\mathrm{aw}_p(\sigma_{R^{F^*}}(p,x))\big]=\mathrm{negl}(n);$$
--   4. hence no serial-fixing reduction is sound, so none is a fully black-box derivation of the transfer assumption from the preparation assumption.
--
--   $F^*$ is inefficient and need not be efficient. No rapid mixing is assumed. The theorem rules out deriving the transfer assumption from the preparation assumption by any reduction that queries the adversary only at the serial number it was given.
--
--   **Formalization Note** The theorem quantifies over every family $\mathrm{Syn}$ and every workspace width $e(n)$; $U^*$ acts as the identity on the workspace. Adversary unitaries act on $s(n)+n+(n+e(n))$ qubits with $R_1$ the challenge register and $R_2$ the next $n$ qubits. A reduction is serial-fixing if its pre-call states have serial register $|p\rangle$ for every adversary unitary and every minted input.
--
--   Differences from the source:
--   - encoding: "for each serial number $p'$, $\mathrm{Syn}_{p'}|0\rangle=|\$_{p'}\rangle$" → required for every $p'$ whose level set is nonempty; other $p'$ get an arbitrary unitary; reason: serial numbers are the values of $I$, and for any other string the banknote is the zero vector and $\Pi_1^{(p')}=0$.
--   - encoding: adversaries "on a serial-number register, a challenge register and further registers" → block-diagonal unitaries on $s(n)+n+(n+e(n))$ qubits for an arbitrary width $e$, with $R_2$ the first $n$ further qubits and $U^*$ the identity on the last $e(n)$; reason: fixes the output convention; $e\equiv0$ is the source's $U^*$ on exactly three registers.
--   - reading: "let $F^*$ be the adversary implemented by $U^*$" → stated as conclusion 1 that $U^*$ is an adversary unitary; reason: the source presupposes it, and stating it makes conclusion 4 a statement about an admissible adversary.
--   - encoding: "$\ge1/\mathrm{poly}(n)$ infinitely often" and "$=\mathrm{negl}(n)$" → the negation of the published `Negligible`, and `Negligible`; reason: the published definitions.
--   - reading: "serial-fixing if the serial-number register is in the basis state $|p\rangle$ at every instance of $U_A$ and $U_A^\dagger$" → for every adversary unitary and every minted input $(p,x)=(I(x),x)$, the state just before every instance is supported on serial register $=p$ at that instance; reason: serial-fixing is a property of $R$ alone, and $R$ receives $(p,x)\leftarrow M_n$.
--   - encoding: soundness "for every $A$, efficient or not" → for every adversary unitary of the width $s(n)+n+(n+e(n))$ on which $R$ places its oracle instances; reason: the wires of $R$'s oracle instances fix the register widths of $U_A$.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 29–30, Theorem 6.9 (Definition 6.8 on p. 29; proof p. 30)

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_SerialFixingReduction
import Definitions.Def_InvariantMoneySecurity_Decomposition_SecurityAssumptions
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- Theorem 6.9, pp. 29–30: under the preparation assumption, for every banknote-preparing
family `Syn` and every workspace width `e`, `U*` is an adversary unitary, `F*` wins with
probability exactly `1`, and every serial-fixing reduction run with `F*` has negligible average
accepted weight; hence no serial-fixing reduction is sound. No rapid mixing is assumed. -/
theorem serial_fixing_barrier (D : Scheme) (hprep : D.Preparation) (e : ℕ → ℕ)
    (Syn : ∀ n, Bits (D.data n).serialBits → Matrix (Bits n) (Bits n) ℂ)
    (hSyn_unitary : ∀ n p, (Syn n p).conjTranspose * Syn n p = 1)
    (hSyn : ∀ n p, ((D.data n).level p).Nonempty →
      (Syn n p).mulVec (basisVector (fun _ => false)) = (D.data n).banknote p) :
    IsAdversary D e (starUnitary D e Syn) ∧
    (∀ n, advWin D e (starUnitary D e Syn) n = 1) ∧
    (∀ R : Reduction D e, R.SerialFixing → Negligible (R.advantage (starUnitary D e Syn))) ∧
    (∀ R : Reduction D e, R.SerialFixing → ¬ R.Sound) := by sorry

end InvariantMoneySecurity.Decomposition.Supplement
