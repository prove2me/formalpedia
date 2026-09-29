-- Prove2me | Theorems.Thm_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
-- name    : ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/e5d5c889-ef70-5d59-a286-f022c1fbeafb
-- title:
--   Universal Katz level-ℓ Weil pairing as ℓ-th root of unity
-- statement:
--   Let $A_0$ be a commutative ring and $\ell$ a prime with $3 \le \ell$ whose image in $A_0$ is a unit, and assume the rule $hℓ$: for every commutative $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$, every Weierstrass variable change $C$ and every $D : \mathrm{LevelPData}\,T$ (a quadruple $x_P,y_P,x_Q,y_Q \in T$), if $D$ is a level-$\ell$ structure on $W$ — the two pairs satisfy the affine Weierstrass equation of $W$, the polynomial $\mathrm{preΨ}_\ell$ of $W$ vanishes at $x_P$ and at $x_Q$, and both $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units — then $D.\mathrm{variableChange}\,C$ is one on $C \bullet W$. Let $L_1, L_3$ be arbitrary level components over $A_0$ and let $P_0$ be a package representing the moduli datum attached to the rigid Weierstrass data of $L_1 \times (\text{level-}\ell) \times L_3$: a commutative $A_0$-algebra $B_0$ together with a point $\mathrm{univ}$ over $B_0$ such that every point over any $A_0$-algebra is the image of $\mathrm{univ}$ under a unique $A_0$-algebra map. Then there exists $\varepsilon \in B_0$ with $\varepsilon^\ell = 1$ such that for every raw datum $u$ over $B_0$ (a Weierstrass curve with unit discriminant, together with a triple of level data satisfying the three level conditions) whose class in the quotient by variable changes is $\mathrm{univ}$, every algebraically closed field $\Omega$ that is an $A_0$-algebra, and every $A_0$-algebra homomorphism $\varphi : B_0 \to \Omega$, writing $x$ for the base change of $u$ along $\varphi$ and using the unit discriminant of $x$ to make its curve elliptic, the value in $\Omega$ of $\mathrm{weilPairing0}$ at level $\ell$ of the two points of the affine curve obtained from the coordinate pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ of the middle level datum of $x$ (taken to be the given affine point when the pair is nonsingular and the point at infinity otherwise) equals $\varphi(\varepsilon)$.
--
--   This is the existence of the relative Weil pairing $e_\ell(P^{\mathrm{univ}}, Q^{\mathrm{univ}}) \in \mu_\ell(B_0)$ of the universal level-$\ell$ basis on a representable rigid Weierstrass moduli problem, together with its compatibility with specialisation at all geometric points. It is used in the analysis of the moduli ring of full level-$\ell$ structures, in particular to locate primitive $\ell$-th roots of unity in quotients of $B_0$ and to compare pairings of points classified by the same homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
    (A₀ : Type u) [CommRing A₀] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (L₁ L₃ : ModularCurve.LevelComponent.{u} A₀)
    (P₀ : LevelModuliPackageAbs A₀ (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.toLevelModuliDatum) :
    ∃ ε : P₀.B₀, ε ^ ℓ = 1 ∧
      ∀ (u : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw P₀.B₀),
        (Quot.mk _ u : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.Pt P₀.B₀) = P₀.univ →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : P₀.B₀ →ₐ[A₀] Ω),
          (letI x := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.mapRing φ u;
           letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
            ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
                (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
                (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) :
              Ω)) = φ ε := by sorry
