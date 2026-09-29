-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3
-- name    : LanglandsTunnell.CubicInduction.forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/92fca0ac-b04c-5775-9b5f-cbf413b1e132
-- title:
--   Whittaker bound on orthogonal compacta extends to all compacta
-- statement:
--   Fix a real number $\theta$ and a natural number $N'$. The assertion is made for every homomorphism $\omega \colon (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ and every function $u \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ (adeles formed from $\mathcal{O}_{\mathbb{Q}}$ and $\mathbb{Q}$) which is continuous, satisfies $u(\gamma g) = u(g)$ for all $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ pushed into $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ by `globalPointsGL`, and satisfies $u(zg) = \omega(z)u(g)$ for every idele $z$ acting through the central scalar embedding. Write $W(g)$ for the Whittaker integral $\int\!\!\int\!\!\int u(n(x,y,z)\,g)\,\psi(-(x+y))$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$, $\psi$ is the standard additive character `psiQ` of $\mathbb{A}_{\mathbb{Q}}$, and each of the three integrals is taken with respect to the additive adelic Haar measure conditioned on the adelic box (infinite box times the integral finite adeles), this being the measure component of `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`. For positive reals $y_1, y_2$ let $a(y_1,y_2)$ denote the image in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, under the archimedean lift [`WhittakerBlock.archRealLift3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18), of the diagonal matrix $\mathrm{diag}(y_1y_2, y_2, 1)$. Consider, for a set $K \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the property: there exists $C \in \mathbb{R}$ with $\|W(a(y_1,y_2)k)\| \le C\,(\min(y_1,1)^{\theta}\max(y_1,1)^{N'})(\min(y_2,1)^{\theta}\max(y_2,1)^{N'})$ for all $k \in K$ and all $y_1, y_2 > 0$. Assuming this property for every compact $K$ all of whose members have archimedean component (via `archComponent3`) lying in `orth3`, i.e. matrices $k$ over the infinite adeles with $k^{\mathsf{T}}k = 1$, the conclusion is that the property holds for every compact $K \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$.
--
--   This is the compactness-and-Iwasawa step which upgrades a two-variable decay estimate for the Whittaker coefficient of an automorphic function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ from compact sets whose archimedean components are orthogonal to arbitrary compact sets, the gain in the unipotent and diagonal directions being absorbed into the constant and the exponents $\theta$, $N'$. It feeds the diagonal Whittaker bound [`LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder`](thm.html#LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder) inside the cubic-induction treatment of the Langlands–Tunnell input to modularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.forall_isCompact_norm_whittaker3_le_of_forall_isCompact_orth3
    (θ : ℝ) (N' : ℕ) :
    ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Continuous u →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
        (∀ k ∈ K, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) →
        ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
            C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ))) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by sorry
