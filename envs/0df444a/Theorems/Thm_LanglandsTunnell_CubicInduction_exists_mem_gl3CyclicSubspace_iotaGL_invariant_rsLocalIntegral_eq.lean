-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
-- name    : LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/311988e9-34d9-5bab-8fe3-38886bd8c072
-- title:
--   K-invariant vector in the cyclic span with unchanged local integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and an additive character $\psi_v$ of the completion $\mathbb{Q}_v$ which is assumed to be the inverse $(\psi_{v}^{\mathrm{std}})^{-1}$ of the standard local character [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). Let $W\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy $W(u(x,y,z)g)=\psi_v(x+y)\,W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$ (upper unipotent equivariance), and assume $W$ is smooth in the sense that some open subgroup $U_v\le \mathrm{GL}_3(\mathbb{Q}_v)$ satisfies $W(gk)=W(g)$ for $k\in U_v$. Let $\varpi$ be an element of the valuation ring whose image in $\mathbb{Q}_v$ is nonzero, and $\ell\in\mathbb{N}$. Then there is $W''$ in the $\mathbb{C}$-span of the right translates of $W$ (the submodule `gl3CyclicSubspace W`) such that: both $W''$ and its dual $\widetilde{W''}(g)=W''(w_3\,{}^t g^{-1})$ are right invariant under $\iota(k)=\mathrm{diag}(k,1)$ for every $k$ in the level-one subgroup $\mathrm{localLevelOne}(\mathcal{O}_{\mathbb{Q}},\mathbb{Q},v,\top)$, the preimage under the local embedding of the finite adelic level-one group at the unit ideal; and, for the Borel structure on $\mathrm{GL}_2(\mathbb{Q}_v)$ given by `localGLBorel`, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$, every Haar measure $\mu_N$ on the range of $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and every $s\in\mathbb{C}$, two statements hold. First, for every $W_2\colon \mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ with $W_2(u(x)g)=\psi^{\mathrm{std}}_{v}(x)W_2(g)$ and $W_2(gk)=W_2(g)$ for $k$ in the same level-one subgroup: if $g\mapsto W(\iota(g))W_2(g)\,|\det g|^{s-1/2}$ is integrable against $\mu_2$ weighted by the quotient density for the unipotent subgroup and $\mu_N$, then so is the corresponding function with $W''$ in place of $W$, and the two local Rankin–Selberg integrals `rsLocalIntegral` with $\delta=\mathrm{modulus}\circ\det$ agree. Second, the same implication and equality hold with $W_2$ replaced by a function $W_2^d$ transforming by $(\psi^{\mathrm{std}}_{v})^{-1}$ and level-one right invariant, and with the first argument $\widetilde{W}\bigl(\iota(g)\,\iota(\mathrm{diag}(\varpi,\varpi)^{-\ell})\bigr)$ compared against $\widetilde{W''}$ at the same point.
--
--   This is the local step that replaces a smooth Whittaker function on $\mathrm{GL}_3(\mathbb{Q}_v)$ by a vector in its cyclic span which is right invariant under $\iota(\mathrm{GL}_2(\mathbb{Z}_v))$, together with its dual, without changing the local Rankin–Selberg integrals against level-one partners on $\mathrm{GL}_2$. It is used in the cubic-induction chapter to normalise the local data entering the primal and dual middle data and the polynomial form of the local functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_invariant_rsLocalIntegral_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (ℓ : ℕ) :
    ∃ W'' : LocalGL3 v → ℂ, W'' ∈ gl3CyclicSubspace W ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W'' (g * iotaGL k) = W'' g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
        dualWhittakerFn3 W'' (g * iotaGL k) = dualWhittakerFn3 W'' g) ∧
      (letI := localGLBorel ℚ v
       haveI := borelSpace_localGLBorel ℚ v
       ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
         (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
         (s : ℂ),
       (∀ (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
          (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
            W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
          (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g),
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (W'' (iotaGL g) * W₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W (iotaGL g)) W₂ =
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => W'' (iotaGL g)) W₂) ∧
       (∀ (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
          (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
            W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
          (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g),
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    (-(ℓ : ℤ)))) * W₂d g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W'' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                    (-(ℓ : ℤ)))) * W₂d g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 W (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d =
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 W'' (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (-(ℓ : ℤ))))) W₂d)) := by sorry
