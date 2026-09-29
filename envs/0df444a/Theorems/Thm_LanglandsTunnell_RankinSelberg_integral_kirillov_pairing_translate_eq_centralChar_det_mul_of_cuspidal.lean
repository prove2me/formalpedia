-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ef249a3c-4c14-550c-abeb-c8f9b4d357cc
-- title:
--   θ₀-invariance of the Kirillov pairing under translation
-- statement:
--   Fix a prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion, let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism and let $N \neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_2 : \mathrm{GL}_2(F) \to \mathbb C$ be a function satisfying: $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for all $x \in F$, $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component at $p$ of the standard adelic additive character; right invariance under the subgroup of $\mathrm{GL}_2(F)$ consisting of those $k$ whose image under the local embedding into $\mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ is, together with its inverse, a level-one matrix for $N$; $w_2 \neq 0$; irreducibility, in the form that $w_2$ lies in the span of the right translates of any nonzero element of the span $W$ of the right translates of $w_2$; admissibility, i.e. for every open subgroup $U$ the $U$-right-invariant vectors of $W$ lie in the span of a finite set of functions; the central character law $w_2(z \cdot g) = \theta_0(z) w_2(g)$ for scalar matrices $z$; and cuspidality, i.e. every $v \in W$ satisfies $v(\mathrm{diag}(y,1)) = 0$ for $y \in F^\times$ of sufficiently small valuation. Equip $F^\times$ with the measure obtained by pulling back along $F^\times \hookrightarrow F$ the measure $|x|^{-1}\,dx$ on $F \setminus \{0\}$, $dx$ being the self-dual additive Haar measure at $p$. Then for every $g \in \mathrm{GL}_2(F)$ and all $u, u' \in W$, the function $t \mapsto u(\mathrm{diag}(t,1))\,u'(\mathrm{diag}(-t,1))\,\theta_0(t)^{-1}$ is integrable on $F^\times$, and $$\int_{F^\times} u(\mathrm{diag}(t,1)g)\,u'(\mathrm{diag}(-t,1)g)\,\theta_0(t)^{-1}\,d^\times t = \theta_0(\det g)\int_{F^\times} u(\mathrm{diag}(t,1))\,u'(\mathrm{diag}(-t,1))\,\theta_0(t)^{-1}\,d^\times t.$$
--
--   This is the $\theta_0$-twisted invariant bilinear pairing on the Kirillov realisation of a cuspidal generic admissible representation of $\mathrm{GL}_2(\mathbb Q_p)$: the pairing transforms under right translation by $g$ through the scalar $\theta_0(\det g)$. It is used in the local Rankin–Selberg analysis, being cited by the results producing a translation-invariant pairing and computing the integral of the translated pairing against an invariant vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal.lean

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

theorem LanglandsTunnell.RankinSelberg.integral_kirillov_pairing_translate_eq_centralChar_det_mul_of_cuspidal
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
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)),
    ∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
    ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      Integrable (fun t : (p.adicCompletion ℚ)ˣ => u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
      (∫ t : (p.adicCompletion ℚ)ˣ, (fun x : GL (Fin 2) (p.adicCompletion ℚ) => u (x * g)) (diagOne t) * (fun x : GL (Fin 2) (p.adicCompletion ℚ) => u' (x * g)) (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        ((θ₀ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
