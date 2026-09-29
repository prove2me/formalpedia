-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant
-- name    : ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a9cf5299-3cf5-50ed-9542-7d453d5241e7
-- title:
--   Descent of swap-invariant level-p Katz forms to level one
-- statement:
--   Let $R$ be a commutative ring, let $p$ be a prime with $p \neq 2$ and with $p$ invertible in $R$, and let $k \in \mathbb{Z}$. Let $F$ be a Katz modular form of weight $k$ and full level $p$ over $R$, that is, a rule assigning to every $R$-algebra $A$, every Weierstrass curve $W$ over $A$ with $\Delta_W$ a unit, and every quadruple $D = (x_P, y_P, x_Q, y_Q)$ of elements of $A$ satisfying `IsLevelPStructure` (both $(x_P,y_P)$ and $(x_Q,y_Q)$ lie on the affine equation of $W$, the polynomial $W.\mathrm{pre}\Psi_p$ vanishes at $x_P$ and at $x_Q$, and $\mathrm{indepElt}\,W\,p\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,p\,x_Q\,x_P$ are units) an element of $A$, compatibly with $R$-algebra maps and satisfying $F(C \bullet W, D^C) = (u^{-1})^k F(W,D)$ for every variable change $C$ with unit $u$. Assume $F$ depends only on the second line: whenever $D, D'$ are such data for the same $W$ and $x_{Q'} \cdot (W.\Psi^2_a)(x_Q) = (W.\Phi_a)(x_Q)$ for some $a$ with $1 \le a \le (p-1)/2$, the values of $F$ at $D$ and $D'$ agree; and assume $F$ is swap-invariant, its value being unchanged when $(x_P,y_P)$ and $(x_Q,y_Q)$ are interchanged. Then there is exactly one level-one Katz modular form $g$ of weight $k$ over $R$ whose pullback to level $p$ (the level-$p$ form that ignores the level structure and returns $g(W)$) equals $F$.
--
--   This is the descent of a full-level-$p$ Katz form invariant under all of $GL_2(\mathbb{F}_p)$ — the two hypotheses encode invariance under the Borel stabiliser of the line spanned by $Q$ together with the Weyl involution — to a form of level one, carried out by faithfully flat descent along the ring of bases of the $p$-torsion; it is the descent step in the proof of Mazur's Lemma II.5.9. It is used in the construction of level-one forms from $\Gamma_0$-type data, via [`ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le`](thm.html#ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) {k : ℤ}
    (F : ModularCurve.KatzLevelPForm R p k) (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    ∃! g : KatzModularForm R k, g.pullbackLevelP p = F := by sorry
