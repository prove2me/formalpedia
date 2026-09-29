-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_apply_jOf_univ_eq_classify_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a021383e-9657-51f0-96bb-1c05115cfffd
-- title:
--   Invertible moduli-problem automorphisms act on the fine moduli ring
-- statement:
--   Let $A$ be a commutative ring and let $D$ be a level-moduli datum over $A$: a rule assigning to every commutative $A$-algebra $T$ a type $D.\mathrm{Pt}\,T$ of points, together with functorial transition maps $D.\mathrm{map}\,f$ along $A$-algebra homomorphisms $f$ (compatible with identities and composition) and a natural invariant $D.\mathrm{jOf} : D.\mathrm{Pt}\,T \to T$ satisfying $D.\mathrm{jOf}(D.\mathrm{map}\,f\,x) = f(D.\mathrm{jOf}\,x)$. Let $P_0$ be an absolute fine moduli package for $D$: a commutative $A$-algebra $B_0 = P_0.B_0$ together with a point $P_0.\mathrm{univ} \in D.\mathrm{Pt}\,B_0$ such that for every $A$-algebra $T$ and every $x \in D.\mathrm{Pt}\,T$ there is a unique $A$-algebra homomorphism $\varphi : B_0 \to T$ with $D.\mathrm{map}\,\varphi\,(P_0.\mathrm{univ}) = x$; write $P_0.\mathrm{classify}\,x$ for this $\varphi$. Let $\sigma, \sigma'$ be automorphisms of the moduli problem, i.e. operations $x \mapsto \sigma.\mathrm{act}\,x$ on $D.\mathrm{Pt}\,T$ commuting with all transition maps and preserving $D.\mathrm{jOf}$, and assume the two hypotheses that $\sigma'.\mathrm{act} \circ \sigma.\mathrm{act}$ and $\sigma.\mathrm{act} \circ \sigma'.\mathrm{act}$ are the identity on $D.\mathrm{Pt}\,T$ for every $A$-algebra $T$. Then there exists an $A$-algebra automorphism $e$ of $B_0$ with $e(D.\mathrm{jOf}\,P_0.\mathrm{univ}) = D.\mathrm{jOf}\,P_0.\mathrm{univ}$ and such that for every $A$-algebra $T$ and every $x \in D.\mathrm{Pt}\,T$ one has $P_0.\mathrm{classify}(\sigma.\mathrm{act}\,x) = (P_0.\mathrm{classify}\,x) \circ e$.
--
--   This is the Yoneda-style statement that an invertible relabelling of a level structure is induced by an automorphism of the ring carrying the fine moduli problem, fixing the image of the $j$-invariant of the universal point. It is the mechanism by which the $\mathrm{GL}_2$-relabellings permute the classifying maps, and it is used in the analysis of minimal primes and residue fields of the fibres of the full-level and $\Gamma_0$-type moduli rings above a given $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_apply_jOf_univ_eq_classify_act_eq
    (A : Type) [CommRing A] (D : ModularCurve.LevelModuliDatum A) (P₀ : LevelModuliPackageAbs A D)
    (σ σ' : D.ProblemAut)
    (hσ : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ'.act (σ.act y) = y)
    (hσ' : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ.act (σ'.act y) = y) :
    ∃ e : P₀.B₀ ≃ₐ[A] P₀.B₀,
      e (D.jOf P₀.univ) = D.jOf P₀.univ ∧
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : D.Pt T),
        P₀.classify (σ.act x) = (P₀.classify x).comp (e : P₀.B₀ →ₐ[A] P₀.B₀) := by sorry
