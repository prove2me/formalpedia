-- Prove2me | Theorems.Thm_MultipartiteREE_Approx_lemma_1
-- name    : MultipartiteREE.Approx.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:28.169568+00:00
-- url     : https://prove2.me/theorems/68ac6d88-677d-4f72-b4e8-ab74626ea6ab
-- title:
--   Lemma 1, p. 20 — relative entropy under a trace-preserving family of positive maps
-- statement:
--   Let $\mathcal H$ be a separable Hilbert space and $\{\Phi_i\}$ a countable collection of positive linear maps from the trace class $\mathfrak T(\mathcal H)$ to itself such that $\sum_i\Phi_i$ is trace preserving. Let $\rho,\sigma$ be states on $\mathcal H$ and put $p_i=\operatorname{Tr}\Phi_i(\rho)$, $\rho_i=p_i^{-1}\Phi_i(\rho)$, $q_i=\operatorname{Tr}\Phi_i(\sigma)$, $\sigma_i=q_i^{-1}\Phi_i(\sigma)$. Then
--
--   $$\sum_i p_iH(\rho_i\|\sigma_i)\le H(\rho\|\sigma),$$
--
--   where $H(\cdot\|\cdot)$ is Lindblad's relative entropy (4). This is the monotonicity used to show that $E_R$ does not increase under selective unilocal operations, hence $\widehat E_R\le E_R$.
--
--   **Formalization Note** "$\sum_i\Phi_i$ is trace preserving" is encoded on positive trace-class operators as $\sum_i\operatorname{Tr}\Phi_i(X)=\operatorname{Tr}X$, which is equivalent for positive maps by linearity. A term with $p_i=0$ contributes $0$ (as $0\cdot\infty=0$ in $[0,+\infty]$). If $q_i=0<p_i$ the Lean $\sigma_i$ is $0$ and the term is $+\infty$; this is consistent, because then $\operatorname{supp}\rho\not\subseteq\operatorname{supp}\sigma$ and $H(\rho\|\sigma)=+\infty$.
-- source:
--   Shirokov, Approximation of multipartite quantum states and the relative entropy of entanglement, arXiv:2103.12111v2, p. 20, Lemma 1

import Mathlib
import Definitions.Def_MultipartiteREE_Approx_Setting

noncomputable section

open Filter Topology
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P01 (homogeneousEntropy generalizedRelativeEntropy)

namespace MultipartiteREE.Approx

theorem lemma_1 {J : Type} [Countable J] {ι : Type} [Countable ι]
    (Phi : ι → Matrix J J ℂ → Matrix J J ℂ) (hPhi : ∀ i, IsPositiveTraceMap (Phi i))
    (htp : ∀ X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      QAlgorithms.Papers.Independent.Frontier18.P01.IsPositive X →
      HasSum (fun i => traceRe (Phi i X)) (traceRe X))
    (rho sigma : State J) :
    ∑' i, ENNReal.ofReal (traceRe (Phi i rho.coefficients)) *
      generalizedRelativeEntropy ((traceRe (Phi i rho.coefficients))⁻¹ • Phi i rho.coefficients)
        ((traceRe (Phi i sigma.coefficients))⁻¹ • Phi i sigma.coefficients) ≤
      generalizedRelativeEntropy rho.coefficients sigma.coefficients := by sorry

end MultipartiteREE.Approx
