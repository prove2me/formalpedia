-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/73d35f2c-1bb2-5dfc-83a6-ea647b80347f
-- title:
--   Non-zero s-independent local Rankin–Selberg integral at a finite place
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the associated completion, and let $\psi$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$ with $\psi \neq 1$. Let $W_3 : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy: $W_3\big(\begin{smallmatrix}1&x&z\\0&1&y\\0&0&1\end{smallmatrix}\, g\big) = \psi^{-1}(x+y)\,W_3(g)$ for all $x,y,z$ and all $g$; right invariance $W_3(gk) = W_3(g)$ for all $k$ in some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$; the cyclicity condition that every non-zero $W$ lying in the $\mathbb{C}$-span of the right translates of $W_3$ has $W_3$ in the span of its own right translates; and $W_3 \neq 0$. Let $W_2 : \mathrm{GL}_2(\mathbb{Q}_v) \to \mathbb{C}$ satisfy $W_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\, g\big) = \psi(x)W_2(g)$, be right invariant under some open subgroup, and have $W_2(1) \neq 0$. Then, with $\mathrm{GL}_2(\mathbb{Q}_v)$ carrying its Borel structure, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ and every Haar measure $\mu_N$ on the image $N$ of $x \mapsto \big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\big)$, there are $n \in \mathbb{N}$, coefficients $c : \mathrm{Fin}\,n \to \mathbb{C}$, elements $k : \mathrm{Fin}\,n \to \mathrm{GL}_3(\mathbb{Q}_v)$ and a constant $C \neq 0$ such that for every $s \in \mathbb{C}$ the function $g \mapsto \big(\sum_i c_i W_3(\iota(g)k_i)\big)W_2(g)\,\mathrm{modulus}(\det g)^{s-1/2}$, where $\iota$ is the upper-left embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N$ and $\mu_N$, and its integral — the local Rankin–Selberg integral `rsLocalIntegral` of $\sum_i c_i W_3(\iota(\cdot)k_i)$ against $W_2$ with modulus factor $\mathrm{modulus} \circ \det$ — equals $C$, independently of $s$.
--
--   This is the local non-vanishing statement for the $\mathrm{GL}_3 \times \mathrm{GL}_2$ Rankin–Selberg zeta integral at a finite place, where the second factor is allowed to be ramified: a suitable finite linear combination of right translates of a Whittaker function on $\mathrm{GL}_3$ pairs with a given $\psi$-Whittaker function on $\mathrm{GL}_2$ to give a non-zero constant in $s$. It feeds the global statement [`LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero), which selects a test vector whose Rankin–Selberg integral does not vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem
LanglandsTunnell.CubicInduction.exists_rsLocalIntegral_sum_translate_eq_const_of_apply_one_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1) (W₃ : LocalGL3 v → ℂ)
    (hW₃ψ : IsGL3PsiWhittakerFn ψ⁻¹ W₃)
    (hW₃U : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₃ (g * k) = W₃ g)
    (hW₃c : ∀ W ∈ gl3CyclicSubspace W₃, W ≠ 0 → W₃ ∈ gl3CyclicSubspace W)
    (hW₃0 : W₃ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = ψ x * W₂ g)
    (hW₂U : ∃ U₂ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (U₂ : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ k ∈ U₂, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 ≠ 0) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → LocalGL3 v) (C : ℂ), C ≠ 0 ∧
      ∀ s : ℂ,
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            ((∑ i, c i * W₃ (iotaGL g * k i)) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => ∑ i, c i * W₃ (iotaGL g * k i)) W₂ = C := by sorry
