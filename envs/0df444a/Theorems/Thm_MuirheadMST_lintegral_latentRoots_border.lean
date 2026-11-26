-- Prove2me | Theorems.Thm_MuirheadMST_lintegral_latentRoots_border
-- name    : MuirheadMST.lintegral_latentRoots_border
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T21:02:28.361082+00:00
-- url     : https://prove2.me/theorems/d0a6db7b-b509-414b-906a-7cb1ec94828f
-- title:
--   Bordering reduction for integrals of latent roots of symmetric matrices
-- statement:
--   Write a symmetric $(m+1)\times(m+1)$ matrix as
--   $$A=\begin{pmatrix} c & b^{\mathsf T}\\ b & A'\end{pmatrix},\qquad c\in\mathbb R,\ b\in\mathbb R^m,\ A'\ \text{symmetric } m\times m.$$
--   For every measurable $h\ge0$ on $\mathbb R^{m+1}$,
--   $$\int h(l(A))\,(dA)=\int \left(\int_{\mathbb R^m\times\mathbb R} h\Big(l\begin{pmatrix} c & b^{\mathsf T}\\ b & \operatorname{diag}(l(A'))\end{pmatrix}\Big)\,db\,dc\right)(dA'),$$
--   where $l(\cdot)$ denotes the decreasing latent roots and $(dA)$ is Lebesgue measure on the upper-triangular entries. That is, after splitting off the border, the inner block may be replaced by the diagonal matrix of its latent roots: conjugating by $\operatorname{diag}(1,H)$ with $H$ orthogonal and $A'=H\operatorname{diag}(l(A'))H^{\mathsf T}$ preserves the latent roots and maps $b\mapsto H^{\mathsf T}b$, which preserves Lebesgue measure.
--
--   **Formalization Note** The bordered matrix is the array `Fin.cons (Fin.cons c b) (fun i => Fin.cons (b i) (A' i))`, with the border in row and column $0$; `symVolume`, `latentRoots`, `diagArray` are from `Definitions.Def_MuirheadMST_Wishart`.
-- source:
--   P. J. Forrester and S. O. Warnaar, The importance of the Selberg integral, arXiv:0710.3981v1 (2007), https://arxiv.org/abs/0710.3981 (page numbers of the arXiv version), p. 15, the bordered matrix (2.30) and the remark following it that, by invariance under orthogonal conjugation, a symmetric matrix is similar to (2.30); proof step for R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982, https://doi.org/10.1002/9780470316559, §3.2.5, Theorem 3.2.17, p. 104

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory

namespace MuirheadMST

theorem lintegral_latentRoots_border (m : ℕ) (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h) :
    ∫⁻ A, h (latentRoots A) ∂(symVolume (m + 1)) =
      ∫⁻ A, (∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
          ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
            (fun i => (Fin.cons (p.1 i) (diagArray (latentRoots A) i) : Fin (m + 1) → ℝ)) :
              Fin (m + 1) → Fin (m + 1) → ℝ)))) ∂(symVolume m) := by sorry

end MuirheadMST
