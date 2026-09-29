-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ad8af360-1bc3-5069-832d-bbbd9202dd8b
-- title:
--   Laurent polynomiality of the dual local Rankin–Selberg integral at level vᵇ
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$, $F = K_v$ the completion, and $\varpi$ an element of the valuation ring whose image in $F$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $b \in \mathbb{N}$, let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$, let $W_3 : \mathrm{GL}_3(F) \to \mathbb{C}$ satisfy $W_3(n(x,y,z)h) = \theta^{-1}(x+y)W_3(h)$ for all $x,y,z \in F$ and $h$, and be right invariant under some open subgroup of $\mathrm{GL}_3(F)$; let $g_3 \in \mathrm{GL}_3(F)$. Let $w_2 : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy $w_2\bigl(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right) g\bigr) = \theta(x) w_2(g)$ and be right invariant under [`AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding `localEmbed` of the finite-adelic level-one subgroup of level $v^b$; let $w_{0}$ be the element of $\mathrm{GL}_2(F)$ with matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. Equip $F$ and $\mathrm{GL}_2(F)$ with their Borel $\sigma$-algebras. Then for all Haar measures $\mu_2$ on $\mathrm{GL}_2(F)$, $\mu_{N}$ on the image of $x \mapsto \left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)$ in $\mathrm{GL}_2(F)$ and $\nu$ on $F^{\times}$, the following holds. Write $\widetilde{W}(h) = W_3(w_3\,{}^{t}h^{-1} g_3)$ for the dual Whittaker function attached to $W_3(\cdot\, g_3)$ (with $w_3$ the long Weyl element of $\mathrm{GL}_3$), $\iota(g) = \mathrm{diag}(g,1)$, and ${}^{t}g^{-1}$ for the transpose of the inverse. Assume the torus-shell vanishing hypothesis: for every $k_0$ in [`AdelicDock.localLevelOne (𝓞 K) K v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), every homomorphism $\eta : F^{\times} \to \mathbb{C}^{\times}$ and every $c \in \mathbb{N}$ such that $\eta$ is trivial on the $c$-th higher units while for each $m < c$ some $m$-th higher unit has $\eta(u) \neq 1$, and $c \le b$, there is a finite set $T \subset \mathbb{Z} \times \mathbb{Z}$ with
--   $$\int_{|u|_v = 1} \Bigl(\int_{K_1} \widetilde{W}\bigl(\iota\bigl(\varpi^{n_2} I \cdot \mathrm{diag}(\varpi^{n_1}u,1)\cdot (k_0\,{}^{t}k^{-1})\bigr)\bigr)\,\mathrm{d}\mu_2(k)\Bigr)\,\eta(u)\,\mathrm{d}\nu(u) = 0$$
--   for all $(n_1,n_2) \notin T$, where $K_1$ is the level-$v^b$ subgroup above and $\varpi^{n_2} I$ is the scalar matrix. Then there exist a polynomial $P \in \mathbb{C}[X]$ and $m \in \mathbb{Z}$ such that for every $s \in \mathbb{C}$, provided the function $g \mapsto \bigl(\widetilde{W}(\iota(g))\cdot |\det g|\, w_2(w_0\,{}^{t}g^{-1})\bigr)\,|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup with $\mu_{N}$, the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of the pair $\bigl(\widetilde{W}\circ\iota,\ g \mapsto |\det g| w_2(w_0\,{}^{t}g^{-1})\bigr)$ with modulus $g \mapsto |\det g|$ at $s$ equals $q^{ms}P(q^{-s})$, where $q$ is the absolute norm of $v$ and $|\cdot|$ denotes `modulus`, the distributive Haar character of $F$.
--
--   This is the local Rankin–Selberg integral for $\mathrm{GL}_3 \times \mathrm{GL}_2$ in the dual (transposed) normalisation, in the shape used by Jacquet–Piatetski-Shapiro–Shalika: under a finiteness hypothesis on the torus-shell integrals of the dual Whittaker function against characters of conductor at most $b$, the integral is a Laurent polynomial in $q^{-s}$. It is obtained from the general statement about left-$N$-invariant products with torus finiteness, applied to the transposed level-$v^b$ group, and it feeds the statements of the local functional equation and of the Laurent-expansion and spanning properties of these integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ) (θ : AddChar (v.adicCompletion K) ℂ)
    (W₃ : GL (Fin 3) (v.adicCompletion K) → ℂ) (hW₃law : IsGL3PsiWhittakerFn θ⁻¹ W₃)
    (hW₃sm : ∃ Uv : Subgroup (GL (Fin 3) (v.adicCompletion K)), IsOpen (Uv : Set (GL (Fin 3) (v.adicCompletion K))) ∧
      ∀ k ∈ Uv, ∀ g : GL (Fin 3) (v.adicCompletion K), W₃ (g * k) = W₃ g)
    (g₃ : GL (Fin 3) (v.adicCompletion K))
    (w₂ : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hw₂law : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)), w₂ (unipotent x * g) = θ x * w₂ g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b), ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₂ (g * k) = w₂ g)
    (w₀p : GL (Fin 2) (v.adicCompletion K))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; 1, 0]) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers K)
                        (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
          (dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g) *
            (((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ) : ℂ) *
              w₂ (w₀p * AutomorphicForm.transposeInvN (Fin 2) g))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ) : ℂ)
              ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
            s (fun g => dualWhittakerFn3 (fun x => W₃ (x * g₃)) (iotaGL g))
            (fun g => ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K)
              : ℝ) : ℂ) * w₂ (w₀p * AutomorphicForm.transposeInvN (Fin 2) g)) =
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
