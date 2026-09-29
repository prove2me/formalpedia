-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
-- name    : LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/463017fb-d2e5-568e-bfe4-8494860064a9
-- title:
--   Level vectors killed by N_{(2,1)}-invariant functionals on I(χ)
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F = \mathbb{Q}_v$ for the completion, let $\chi_0,\chi_1,\chi_2$ be homomorphisms $F^{\times}\to\mathbb{C}^{\times}$, and let $b$ be a natural number such that for each $i$ there is a unit $u$ with $|u| = 1$ and ($b = 0$, or $|u-1|\le \exp(-b)$) for which $\chi_i(u)\neq 1$. Let $\Phi : GL_3(F)\to\mathbb{C}$ lie in `principalSeries3`, i.e. $\Phi$ is locally constant, left invariant under the upper unipotent matrices $n(x,y,z)$, and satisfies $\Phi(\mathrm{diag}(a_0,a_1,a_2)g) = \chi_0(a_0)\chi_1(a_1)\chi_2(a_2)\,(\|a_0\|/\|a_2\|)\,\Phi(g)$. Assume further that $\Phi$ is invariant under right translation by $\mathrm{diag}(u,1,1)$ for every $u$ with $|u| = 1$, by $n(s,0,0)$ for every $s$ with $|s|\le\exp(-b)$, and by the lower unipotent matrix with $(2,1)$ entry $s$ for every such $s$. Then there is a natural number $c$ with the following property: every $\mathbb{C}$-linear functional $\Lambda$ on the principal series module which is invariant under right translation by $n(0,Y_1,Y_0)$ for all $Y$ with $|Y_i|\le\exp(c)$ satisfies $\Lambda(\Phi) = 0$.
--
--   This is the representation-theoretic heart of the vanishing of the Jacquet module image, along the unipotent radical of the standard parabolic of type $(2,1)$, of a vector of a $GL_3$ principal series all three of whose inducing characters are ramified beyond level $b$ and which is fixed by the corresponding mirabolic congruence data; classically it follows from the Bernstein–Zelevinsky geometric lemma together with Casselman's description of Jacquet modules. It is used in the transposed-inverse variant of the same statement and in the proof that the type integrals vanish far out in the second torus direction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g) :
    ∃ c : ℕ, ∀ Λ : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ) →ₗ[ℂ] ℂ,
      (∀ (F : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
        (∀ i, Valued.v (Y i) ≤ WithZero.exp (c : ℤ)) →
        Λ ⟨LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := ℂ)
              (LanglandsTunnell.CubicInduction.radicalP21 Y) F,
            LanglandsTunnell.CubicInduction.rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F) →
      Λ ⟨Φ, hΦ⟩ = 0 := by sorry
