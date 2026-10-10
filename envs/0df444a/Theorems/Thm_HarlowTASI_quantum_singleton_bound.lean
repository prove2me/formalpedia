-- Prove2me | Theorems.Thm_HarlowTASI_quantum_singleton_bound
-- name    : HarlowTASI.quantum_singleton_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:12:31.383129+00:00
-- url     : https://prove2.me/theorems/55b34047-7f59-4cda-966d-842b17602d7c
-- title:
--   Eq. (4.25) — quantum Singleton bound $m\ge (n+k)/2$ for symmetric erasure codes
-- statement:
--   Encode $k\ge1$ logical qudits into $n$ physical qudits, each of dimension $d\ge2$: the code subspace is the image of an isometry $V:(\mathbb C^d)^{\otimes k}\to(\mathbb C^d)^{\otimes n}$. Say that the logical information is **accessible** from a set $A$ of physical qudits if every logical operator $\tilde O$ has a representative $O_A$ supported on $A$ with $O_A|\tilde\psi\rangle=\tilde O|\tilde\psi\rangle$ and $O_A^\dagger|\tilde\psi\rangle=\tilde O^\dagger|\tilde\psi\rangle$ for all code states (condition (1) of Theorem 4.1 with $R=A$). Assume, as in the lectures, that whether a set of qudits gives access to the logical information depends only on the number of qudits in it. Then every set $A$ from which the information is accessible satisfies
--   $$|A|\ \ge\ \frac{n+k}{2};$$
--   equivalently, the smallest such number $m$ obeys the quantum Singleton bound $m\ge\frac{n+k}{2}$ (4.25).
--
--   This bound quantifies how large a code subspace can be while remaining correctable, and in the lectures it is checked against the three-qutrit code ($n=3$, $k=1$, $m=2$).
--
--   **Formalization Note** Qudits are indexed by `Fin n`, a set of qudits is a `Finset (Fin n)`, and the symmetry assumption is stated as: any two sets of equal cardinality are either both accessible or both not. The hypotheses $d\ge2$ and $k\ge1$ are implicit in the lectures (a qudit is a $d$-state system carrying information; for $d=1$ or $k=0$ the code space is one-dimensional, everything is accessible from the empty set, and the bound fails).
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §4.3, pp. 29–30, eqs. (4.21)–(4.25) (quantum Singleton bound).

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

namespace HarlowTASI
theorem quantum_singleton_bound {n d k : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
    (V : Matrix (Fin n → Fin d) (Fin k → Fin d) ℂ) (hV : IsIsometry V)
    (hsymm : ∀ A B : Finset (Fin n), A.card = B.card →
      (AccessibleFrom V A ↔ AccessibleFrom V B))
    (A : Finset (Fin n)) (hA : AccessibleFrom V A) :
    n + k ≤ 2 * A.card := by sorry
end HarlowTASI
