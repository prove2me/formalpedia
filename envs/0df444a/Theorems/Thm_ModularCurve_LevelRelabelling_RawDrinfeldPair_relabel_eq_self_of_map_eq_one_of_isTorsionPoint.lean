-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint
-- name    : ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_self_of_map_eq_one_of_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/40f28184-87c5-52cf-81a0-47e5a701f820
-- title:
--   Relabelling by g ≡ 1 mod n fixes n-torsion pairs
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be an element of `GroupLaws A`, i.e. a family assigning to each $A$-algebra $T$ and each projective Weierstrass curve $W$ over $T$ with $\Delta_W$ a unit a relative group law on the projective plane model scheme of $W$ over $\operatorname{Spec} T$. Let $T$ be an $A$-algebra and let $x$ be a raw Drinfeld pair over $T$, that is a projective Weierstrass curve $x.\mathrm{curve}$ over $T$ together with two sections $x.P$, $x.Q$ of its projective model over the identity of the base; assume $\Delta_{x.\mathrm{curve}}$ is a unit, witnessed by $h\Delta$. Let $n$ be a natural number and assume that $x.P$ and $x.Q$ are $n$-torsion for the group law $G = \mathcal G\,T\,x.\mathrm{curve}\,h\Delta$, i.e. $G.\mathrm{nsmul}\,n\,x.P = G.\mathrm{one}$ and likewise for $x.Q$, both taken over the identity morphism of the base. Let $g$ be a $2 \times 2$ integer matrix whose entrywise reduction along $\mathbb Z \to \mathbb Z/n$ is the identity matrix. Then the relabelled pair $\big(x.\mathrm{curve},\; [g_{00}]x.P + [g_{10}]x.Q,\; [g_{01}]x.P + [g_{11}]x.Q\big)$, the $\mathbb Z$-linear combinations being formed with $G$, equals $x$ as a raw Drinfeld pair.
--
--   This is the statement that the right action of $\mathrm{GL}_2(\mathbb Z)$ by relabelling on pairs of $n$-torsion sections factors through $\mathrm{GL}_2(\mathbb Z/n)$, in the form that matrices congruent to the identity modulo $n$ act trivially. It is used in the construction of full level structures on Weierstrass moduli data, where it shows that the class of a relabelled pair is unchanged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_self_of_map_eq_one_of_isTorsionPoint.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_eq_self_of_map_eq_one_of_isTorsionPoint
    {A : Type u} [CommRing A] (𝒢 : GroupLaws A)
    {T : Type u} [CommRing T] [Algebra A T]
    (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) (n : ℕ)
    (hP : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.P) (hQ : (𝒢 T x.curve hΔ).IsTorsionPoint (𝟙 _) n x.Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.map (Int.castRingHom (ZMod n)) = 1) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ = x := by sorry
