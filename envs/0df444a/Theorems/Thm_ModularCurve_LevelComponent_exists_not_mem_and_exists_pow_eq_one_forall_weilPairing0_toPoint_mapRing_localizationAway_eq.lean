-- Prove2me | Theorems.Thm_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
-- name    : ModularCurve.LevelComponent.exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/4b028388-7078-5743-af7d-65829ef0d5b1
-- title:
--   Local constancy of the Weil pairing of a level-ℓ basis
-- statement:
--   Let $A_0$ be a commutative ring and $\ell$ a prime with $\ell \ge 3$ whose image in $A_0$ is a unit. Assume the compatibility hypothesis `hℓ`: for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$, every variable change $C$ and every quadruple $D = (x_P,y_P,x_Q,y_Q)$ in $T$, if $D$ is a level-$\ell$ structure on $W$ — both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation, $\Psi_\ell$-type vanishing $(W.\mathrm{pre}\Psi\,\ell)(x_P) = (W.\mathrm{pre}\Psi\,\ell)(x_Q) = 0$ holds, and the two independence elements $\prod_{1 \le a \le (\ell-1)/2}(x\,(W.\Psi^2_a)(x_0) - (W.\Phi_a)(x_0))$ for $(x_0,x) = (x_P,x_Q)$ and $(x_Q,x_P)$ are units — then the transported quadruple $D.\mathrm{variableChange}\,C$ is a level-$\ell$ structure on $C \bullet W$. Let $L_1, L_3$ be level components over $A_0$, let $B$ be an $A_0$-algebra, and let $w$ be a raw datum for $L_1 \times (\Gamma(\ell) \times L_3)$ over $B$, namely a Weierstrass curve over $B$ with unit discriminant together with level data in each of the three factors satisfying the respective `IsLevel` predicates, the middle one being a level-$\ell$ structure in the above sense. Let $\mathfrak p \subset B$ be prime. Then there are $f \in B \setminus \mathfrak p$ and $\varepsilon \in B[1/f]$ with $\varepsilon^\ell = 1$ such that for every algebraically closed field $\Omega$ that is an $A_0$-algebra and every $A_0$-algebra homomorphism $\varphi : B[1/f] \to \Omega$, the following holds. Write $x$ for the base change of $w$ along $B \to B[1/f] \xrightarrow{\varphi} \Omega$, so that $x$ consists of a Weierstrass curve $x.\mathrm{curve}$ over $\Omega$ with unit discriminant, hence elliptic, and a level-$\ell$ quadruple $(x_P,y_P,x_Q,y_Q)$ over $\Omega$; let $P$ and $Q$ be the affine points of $(x.\mathrm{curve})$ base changed to $\Omega$ attached to $(x_P,y_P)$ and $(x_Q,y_Q)$ by [`ModularCurve.LevelRelabelling.toPoint`](def/ModularCurve_LevelRelabelling.html#L22) (the point `some` if the coordinates are nonsingular, and $0$ otherwise). Then the value in $\Omega$ of $\mathrm{weilPairing0}$ of $x.\mathrm{curve}$ over $\Omega$ at $n = \ell$ on the pair $(P,Q)$ — the unit $c$ with $\mathrm{transEquiv}(P)(\mathrm{weilFun}\,\ell\,Q) = c \cdot \mathrm{weilFun}\,\ell\,Q$ when such a $c$ exists, and $1$ otherwise — equals $\varphi(\varepsilon)$.
--
--   This is the Zariski-local form, at a prime of the base, of the relative Weil pairing on a moduli problem carrying a Katz level-$\ell$ structure, together with its compatibility with specialisation at geometric points: the pairing of the level-$\ell$ basis is given, after inverting one element of the base, by a single $\ell$-th root of unity of the localised ring. It is used by [`ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ`](thm.html#ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ), where the local roots of unity are glued into one element of the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelComponent.exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
    (A₀ : Type u) [CommRing A₀] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (L₁ L₃ : ModularCurve.LevelComponent.{u} A₀)
    (B : Type u) [CommRing B] [Algebra A₀ B]
    (w : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw B)
    (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ f : B, f ∉ 𝔭 ∧ ∃ ε : Localization.Away f, ε ^ ℓ = 1 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : Localization.Away f →ₐ[A₀] Ω),
        (letI x := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.mapRing
            (φ.comp (IsScalarTower.toAlgHom A₀ B (Localization.Away f))) w;
         letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
          ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) :
            Ω)) = φ ε := by sorry
