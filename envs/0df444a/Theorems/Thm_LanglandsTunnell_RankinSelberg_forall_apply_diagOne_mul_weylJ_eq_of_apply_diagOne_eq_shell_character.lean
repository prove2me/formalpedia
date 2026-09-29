-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
-- name    : LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d70461d1-9036-5479-8f22-0fcb8600dcec
-- title:
--   Weyl element on a pure Kirillov vector of one shell
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion, and let $\theta_0\colon F^\times\to\mathbb C^\times$ be a character and $N\neq 0$ an ideal. Let $w_{2}\colon \mathrm{GL}_2(F)\to\mathbb C$ satisfy: $w_2(u(x)g)=\psi_p(x)w_2(g)$ for the standard local additive character $\psi_p$ and $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the subgroup $\mathrm{localLevelOne}$ of level $N$ (the pullback along the local embedding into $\mathrm{GL}_2$ of the finite adeles of the finite level-one subgroup); $w_2\neq 0$; every nonzero $w$ in the span $V$ of the right translates of $w_2$ has $w_2$ in the span of its own right translates; for each open subgroup $U$ a finite set spanning the $U$-right-invariant vectors of $V$; and $w_2(\mathrm{diag}(z,z)g)=\theta_0(z)w_2(g)$. Let $w_J$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, let $\varpi$ be an element of the valuation ring of valuation $\exp(-1)$, nonzero in $F$, and let $\eta,\lambda\colon F^\times\to\mathbb C^\times$ be characters with $\lambda=\eta^{-1}$ on the units of valuation $1$. Assume constants $E\in\mathbb C$, $e\in\mathbb Z$ satisfy the shell relation: for all $w\in V$ and $n\in\mathbb Z$, $\int_{|u|=1} w(\mathrm{diag}(\varpi^n u,1)w_J)\lambda(u)^{-1}\theta_0(u)^{-1}\,d^\times u = E\,\theta_0(\varpi)^n\int_{|u|=1} w(\mathrm{diag}(\varpi^{e-n}u,1))\lambda(u)\,d^\times u$, the measure being the pullback along $u\mapsto u$ of the multiplicative modification of the self-dual Haar measure at $p$, with the Borel structure $\mathrm{localBorel}$. Then for $m\in\mathbb Z$ and $v\in V$ with $v(\mathrm{diag}(y,1))=\eta(y\varpi^{-m})$ when $|y|=\exp(-m)$ and $0$ otherwise, one has for every $y\in F^\times$ that $v(\mathrm{diag}(y,1)w_J)$ equals $E\,\theta_0(\varpi)^{e-m}\,(\theta_0\eta^{-1})(y\varpi^{-(e-m)})$ when $|y|=\exp(-(e-m))$, and $0$ otherwise.
--
--   This is the local statement that the Weyl element sends the pure Kirillov vector of type $(\eta,m)$ to $E\,\theta_0(\varpi)^{e-m}$ times the pure vector of type $(\theta_0\eta^{-1},e-m)$, the $\varepsilon$-factor form of the local functional equation in the Kirillov model. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, by the computation of the Kirillov pairing under translation for cuspidal vectors and by the determination of the shell constants from $w_J^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (η lam : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → lam u = (η u)⁻¹)
    (E : ℂ) (e : ℤ)
    (hKW : letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((lam u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
            E * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (e - n) * u)) * ((lam u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
    (m : ℤ) (v : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hv : v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (hvK : ∀ y : (p.adicCompletion ℚ)ˣ, v (diagOne y) =
      if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-m) then ((η (y * (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-m)) : ℂˣ) : ℂ) else 0) :
    ∀ y : (p.adicCompletion ℚ)ˣ, v (diagOne y * wJ) =
      E * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ (e - m) *
        (if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(e - m)) then
          (((θ₀ * η⁻¹) (y * (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-(e - m))) : ℂˣ) : ℂ) else 0) := by sorry
