-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/fa445247-074c-518a-8076-e0837dc33e37
-- title:
--   K-averaging commutes with the θ₀-twisted Kirillov pairing
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion, and let $\theta_0 : F^\times \to \mathbb C^\times$ be a multiplicative homomorphism. Let $N \neq \bot$ be an ideal of $\mathcal O_{\mathbb Q}$ and let $w_2 : \mathrm{GL}_2(F) \to \mathbb C$ be a function satisfying: the Whittaker transformation law $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for the upper unipotent $n(x) = \binom{1\ x}{0\ 1}$ and the local component $\psi_p$ of the standard adelic additive character; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm f})$ of the level-$N$ congruence subgroup `finiteLevelOne`; $w_2 \neq 0$; irreducibility, in the form that every nonzero $w$ in the $\mathbb C$-span $V$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; admissibility, in the form that for every open subgroup $U$ there is a finite set $B$ of functions spanning all $U$-right-invariant elements of $V$; the central character law $w_2(z\cdot 1_2 \cdot g) = \theta_0(z) w_2(g)$; and cuspidality, namely that each $v \in V$ admits $N_0 \in \mathbb Z$ with $v(\mathrm{diag}(y,1)) = 0$ whenever $|y| \le \exp N_0$. With $F$ and $\mathrm{GL}_2(F)$ given their Borel structures, let $\mu_2$ be a Haar measure on $\mathrm{GL}_2(F)$ and $K \le \mathrm{GL}_2(F)$ an open compact subgroup with $\theta_0(\det k) = 1$ for all $k \in K$. Then for all $u, u' \in V$ with $u'$ right $K$-invariant, integration over $F^\times$ against the multiplicative measure obtained by pulling back along $F^\times \hookrightarrow F$ the measure `mulMeasure` (the self-dual additive Haar measure `selfDualHaarAt` restricted away from $0$, with density the inverse module $|x|^{-1}$) gives $$\int_{F^\times} \Bigl(\int_K u(\mathrm{diag}(t,1)k)\,d\mu_2(k)\Bigr) u'(\mathrm{diag}(-t,1))\,\theta_0(t)^{-1} = \mu_2(K) \int_{F^\times} u(\mathrm{diag}(t,1))\,u'(\mathrm{diag}(-t,1))\,\theta_0(t)^{-1},$$ with $\mu_2(K)$ read as a real number.
--
--   This is the invariance of the $\theta_0$-twisted Kirillov pairing on a cuspidal local Whittaker model under averaging a vector over a compact open subgroup $K$ contained in the kernel of $\theta_0 \circ \det$: the averaging operator may be moved off the first argument at the cost of the factor $\mu_2(K)$. It serves the local Rankin–Selberg input, and is used in the construction of a vector whose $K$-translate integrals compute the pairing ([`LanglandsTunnell.RankinSelberg.exists_mem_forall_setIntegral_translate_eq_kirillov_pairing_of_cuspidal`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_forall_setIntegral_translate_eq_kirillov_pairing_of_cuspidal)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal.lean

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

theorem LanglandsTunnell.RankinSelberg.integral_setIntegral_translate_kirillov_pairing_eq_mul_of_invariant_of_cuspidal
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
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      (∀ k ∈ K, θ₀ (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ u ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ u' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        (∀ k ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u' (g * k) = u' g) →
        (∫ t : (p.adicCompletion ℚ)ˣ,
            (∫ k in (K : Set (GL (Fin 2) (p.adicCompletion ℚ))), u (diagOne t * k) ∂μ₂) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
          ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∫ t : (p.adicCompletion ℚ)ˣ, u (diagOne t) * u' (diagOne (-t)) * (((θ₀ t : ℂˣ) : ℂ))⁻¹
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
