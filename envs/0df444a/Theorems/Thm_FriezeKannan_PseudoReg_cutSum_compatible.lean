-- Prove2me | Theorems.Thm_FriezeKannan_PseudoReg_cutSum_compatible
-- name    : FriezeKannan.PseudoReg.cutSum_compatible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:08.908+00:00
-- url     : https://prove2.me/theorems/f8932311-93db-4116-858b-f1af02afd36c
-- title:
--   §5.1, p. 204 — D = D⁽¹⁾ + ⋯ + D⁽ˢ⁾ is compatible with the atom partition of the R_t, C_t
-- statement:
--   Let $V$ be a finite set, and let $\mathbf D^{(t)}=\mathrm{CUT}(R_t,C_t,d_t)$, $t=1,\dots,s$, be cut matrices on $V\times V$, with $R_t,C_t\subseteq V$ and $d_t\in\mathbb R$. Let $\mathcal P=V_1,\dots,V_k$ be the coarsest partition of $V$ such that each $R_t$ and each $C_t$ is a union of parts. Then
--   $$\mathbf D=\mathbf D^{(1)}+\mathbf D^{(2)}+\dots+\mathbf D^{(s)}$$
--   is compatible with $\mathcal P$: $\mathbf D(p,q)$ is constant over every block $V_i\times V_j$.
--
--   This is the property of the cut decomposition that lets Lemma 7(a) be applied with $\mathbf M=\mathbf D$ in the proof of claim (50).
--
--   **Formalization Note.** The partition is Mathlib's `Finpartition.atomise` of the family $\{R_1,\dots,R_s,C_1,\dots,C_s\}$, whose parts are the nonempty atoms of the family.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 204, §5.1, "note that D is compatible with P"

import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem cutSum_compatible {V : Type*} [Fintype V] [DecidableEq V]
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ) :
    Compatible (atomPartition Rs Cs) (cutSum Rs Cs d) := by sorry

end FriezeKannan.PseudoReg
