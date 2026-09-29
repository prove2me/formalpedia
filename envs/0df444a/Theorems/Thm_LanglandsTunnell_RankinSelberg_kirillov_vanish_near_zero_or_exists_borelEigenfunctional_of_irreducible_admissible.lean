-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
-- name    : LanglandsTunnell.RankinSelberg.kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/f39b75ee-af4b-5d53-b89f-3520a79a436f
-- title:
--   Kirillov vanishing or Borel eigenfunctional dichotomy for GL₂(ℚₚ)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion, let $\theta_0 : F^\times \to \mathbb C^\times$ be a character, and let $N \neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_2 : GL_2(F) \to \mathbb C$ satisfy: $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for all $x \in F$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component at $p$ of the standard additive character of the adeles of $\mathbb Q$; right invariance $w_2(gk) = w_2(g)$ for $k$ in the subgroup of $GL_2(F)$ pulled back, along the embedding of $GL_2(F)$ into $GL_2$ of the finite adeles, from the level-one subgroup of level $N$; $w_2 \neq 0$; irreducibility, in the form that every non-zero $w$ in the span $W$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; admissibility, in the form that for each open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions whose span contains every right $U$-invariant element of $W$; and $w_2(z\cdot 1 \cdot g) = \theta_0(z) w_2(g)$ for scalars $z \in F^\times$. Then either (i) every $v \in W$ vanishes near zero along the torus: there is $N_0 \in \mathbb Z$ with $v(\mathrm{diag}(y,1)) = 0$ whenever $|y| \le \exp N_0$; or (ii) there are characters $\chi_1, \omega_1 : F^\times \to \mathbb C^\times$ and a $\mathbb C$-linear functional $\ell_B$ on the space of all functions $GL_2(F) \to \mathbb C$ which is non-zero at some element of $W$ and satisfies, for all $v \in W$, invariance under right translation by $n(x)$, and scaling by $\chi_1(a)$ and by $\omega_1(a)$ under right translation by $\mathrm{diag}(a,1)$ and by the scalar matrix $a \cdot 1$ respectively.
--
--   This is the local supercuspidal/non-supercuspidal dichotomy at $p$, in the shape used for Whittaker models realised by right translation: either all Kirillov functions vanish in a neighbourhood of zero, or the representation carries a non-zero Borel eigenfunctional, i.e. a character of the Borel subgroup occurs as a quotient. It feeds the Rankin–Selberg arguments establishing functional equations for the Godement–Jacquet and torus zeta integrals in the principal series case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible
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
    :
    (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) ∨
      (∃ (χ₁ ω₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (ℓB : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
        (∃ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB v ≠ 0) ∧
        (∀ (x : (p.adicCompletion ℚ)), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * unipotent x)) = ℓB v) ∧
        (∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v) ∧
        (∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)) := by sorry
