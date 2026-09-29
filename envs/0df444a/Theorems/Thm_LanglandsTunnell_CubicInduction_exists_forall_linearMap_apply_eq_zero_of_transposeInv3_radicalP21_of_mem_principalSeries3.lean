-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
-- name    : LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/158a9ca5-4f2d-5fc0-a33f-e90fabe13fde
-- title:
--   Vanishing along the opposite (2,1)-radical for ramified GL₃ principal series
-- statement:
--   Let $v$ be a height one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, and let $\chi_0,\chi_1,\chi_2$ be characters, i.e. monoid homomorphisms $F^{\times} \to \mathbb{C}^{\times}$, and $b$ a natural number. Assume each $\chi_i$ is non-trivial on `higherUnitsAt ℚ v b`, the set of units $u$ with $\lvert u\rvert = 1$ and, unless $b = 0$, $\lvert u - 1\rvert \le \exp(-b)$. Let $\Phi : GL_3(F) \to \mathbb{C}$ lie in `principalSeries3 v χ`, the $\mathbb{C}$-subspace of functions that are locally constant, satisfy $\Phi(n g) = \Phi(g)$ for every upper unipotent $n = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$, and satisfy $\Phi(\mathrm{diag}(a_0,a_1,a_2)\,g) = \chi_0(a_0)\chi_1(a_1)\chi_2(a_2)\,(\lVert a_0\rVert/\lVert a_2\rVert)\,\Phi(g)$ for $a_i \in F^{\times}$. Assume further that $\Phi$ is invariant under right translation by $\mathrm{diag}(u,1,1)$ for every unit $u$ with $\lvert u\rvert = 1$, by $\begin{pmatrix}1&s&0\\0&1&0\\0&0&1\end{pmatrix}$ and by $\begin{pmatrix}1&0&0\\s&1&0\\0&0&1\end{pmatrix}$ for every $s \in F$ with $\lvert s\rvert \le \exp(-b)$. Then there is a natural number $c$ such that every $\mathbb{C}$-linear form $\Lambda$ on `principalSeries3 v χ` which is invariant under right translation by all matrices $(\,\begin{pmatrix}1&0&Y_0\\0&1&Y_1\\0&0&1\end{pmatrix}^{-1})^{\mathsf{T}}$, i.e. by the lower unipotent elements with last row $(-Y_0,-Y_1,1)$, with $\lvert Y_i\rvert \le \exp(c)$, annihilates $\Phi$.
--
--   This is the statement that a vector of a principal series of $GL_3(F)$ whose inducing characters are all ramified of depth at least $b$, and which is fixed by the indicated level-$b$ subgroup inside the $GL_2$-block, dies in the Jacquet module along the parabolic opposite to the standard one of type $(2,1)$: invariance of a linear form under a large enough compact piece of the opposite unipotent radical forces it to kill $\Phi$. It is the transpose-inverse counterpart of [`LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3), and it is used to control the type integrals of the dual Whittaker function far out in the second torus direction, in [`LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_snd`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_snd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
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
              (LanglandsTunnell.CubicInduction.transposeInv3
                (LanglandsTunnell.CubicInduction.radicalP21 Y)) F,
            LanglandsTunnell.CubicInduction.rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F) →
      Λ ⟨Φ, hΦ⟩ = 0 := by sorry
