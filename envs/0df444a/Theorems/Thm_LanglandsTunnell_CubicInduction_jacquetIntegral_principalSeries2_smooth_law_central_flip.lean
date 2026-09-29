-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip
-- name    : LanglandsTunnell.CubicInduction.jacquetIntegral_principalSeries2_smooth_law_central_flip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b6e3fe64-653f-5608-9280-554beefb3c77
-- title:
--   Smoothness and Whittaker laws of a GL₂ Jacquet integral
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the completion at $p$. Let $\mu = (\mu_0,\mu_1)$ be a pair of homomorphisms $F^\times \to \mathbb{C}^\times$, and let $\varphi : GL_2(F) \to \mathbb{C}$ lie in `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, invariant under left translation by the upper unipotent matrices $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\,\varphi(g)$ for units $a_0,a_1$. Let $w_0 \in GL_2(F)$ have underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $d \in GL_2(F)$ underlying matrix $\mathrm{diag}(1,-1)$. With the Borel structure on $F$, set $W'(k) = \int_F \psi(x)\,\varphi(w\,n(x)\,k)\,dx$, where $\psi$ is the local component at $p$ of the standard additive character, $dx$ is the self-dual Haar measure (the normalised additive Haar measure `selfDualHaarAt`) and $w$ is the antidiagonal element `antidiagonal2 p`. The assertion is a seven-fold conjunction: $\varphi$ is invariant under right translation by some open subgroup of $GL_2(F)$; $W'$ is locally constant; $W'(n(a)k) = \psi(-a)W'(k)$ for all $a \in F$, $k$, stated for both the `unipotent` and the `unipotentGL2` spellings of $n(a)$ (in the second with the factor $\psi^{-1}(a)$); $W'(zk) = \mu_0(z)\mu_1(z)W'(k)$ for every scalar matrix $z$ with $z \in F^\times$; and, for the flipped slot $k \mapsto W'(w_0\,{}^{\mathsf t}(dk)^{-1})$, the law $W'(w_0\,{}^{\mathsf t}(d\,n(t)k)^{-1}) = \psi(-t)\,W'(w_0\,{}^{\mathsf t}(dk)^{-1})$ together with local constancy of that function of $k$.
--
--   This collects the elementary properties of the raw Jacquet (Whittaker) integral attached to a vector in a normalised principal series of $GL_2$ over a $p$-adic field: smoothness, the $\psi^{-1}$-Whittaker transformation law under the unipotent radical, the central character, and the corresponding law for the transpose-inverse (contragredient) slot. It feeds the local computations of Rankin–Selberg integrals for principal-series and cuspidal data used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.jacquetIntegral_principalSeries2_smooth_law_central_flip
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1]) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ (g * k) = φ g) ∧

    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotent a * k)) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-a) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧
    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotentGL2 a * k)) ∂(selfDualHaarAt ℚ p)) = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ a * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (zc : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * k)) ∂(selfDualHaarAt ℚ p)) = ((μ 0 zc : ℂˣ) : ℂ) * ((μ 1 zc : ℂˣ) : ℂ) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (t : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * (unipotent t * k)))) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-t) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) ∧
    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) := by sorry
