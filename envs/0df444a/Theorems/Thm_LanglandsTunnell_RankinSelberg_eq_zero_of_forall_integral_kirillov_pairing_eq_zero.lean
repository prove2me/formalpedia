-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_eq_zero_of_forall_integral_kirillov_pairing_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.eq_zero_of_forall_integral_kirillov_pairing_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/6ca4076b-e16b-53b7-8738-fb67f727c60d
-- title:
--   Non-degeneracy of the θ₀-twisted Kirillov pairing
-- statement:
--   Let $p$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, with completion $F = \mathbb{Q}_p$, let $\theta_0 : F^\times \to \mathbb{C}^\times$ be a multiplicative character, and let $N \neq 0$ be an ideal of the ring of integers. Let $w_2 : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy: $w_2\!\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)g) = \psi_p(x)\,w_2(g)$, where $\psi_p$ is the standard adelic additive character composed with the embedding of $F$ at $p$; right invariance under the subgroup of $\mathrm{GL}_2(F)$ whose image under the local embedding into $\mathrm{GL}_2$ of the finite adeles, together with its inverse, consists of level-one matrices for $N$; $w_2 \neq 0$; an irreducibility condition, namely that for every nonzero $w$ in the span $W$ of the right translates $g \mapsto w_2(gh)$, the function $w_2$ lies in the span of the right translates of $w$; an admissibility condition, namely that for every open subgroup $U$ there is a finite set $B$ of functions spanning all $U$-right-invariant elements of $W$; and $w_2(\mathrm{diag}(z,z)\,g) = \theta_0(z)\,w_2(g)$ for $z \in F^\times$. Then, for $u' \in W$: if for every $u \in W$ the integral over $F^\times$ of $u(\mathrm{diag}(t,1))\,u'(\mathrm{diag}(-t,1))\,\theta_0(t)^{-1}$ vanishes, with respect to the measure obtained by pulling back along $F^\times \hookrightarrow F$ the measure $\|x\|^{-1}$ times the self-dual additive Haar measure of $F$ restricted to $F \setminus \{0\}$ (the Borel structure being used on $F$), then $u' = 0$.
--
--   This is the non-degeneracy of the $\theta_0$-twisted pairing on the Kirillov realisation of an irreducible admissible generic representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ with central character $\theta_0$, realised inside a $\psi$-Whittaker model of level $K_1(N)$. It is used in the local Rankin–Selberg input to the Langlands–Tunnell argument, where the pairing is matched with a family of translated local integrals of a cuspidal form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_eq_zero_of_forall_integral_kirillov_pairing_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker
open NumberField.AdelicLevel (diagOne)
open scoped Classical

theorem LanglandsTunnell.RankinSelberg.eq_zero_of_forall_integral_kirillov_pairing_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        (∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0) →
      u' = 0 := by sorry
