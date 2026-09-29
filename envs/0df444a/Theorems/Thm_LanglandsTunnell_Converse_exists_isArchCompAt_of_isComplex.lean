-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex
-- name    : LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/a8d76488-9d03-5f2f-9a8a-75e9c250b36a
-- title:
--   Archimedean local component at a complex place is a quasi-character
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K$, let $\mu : \mathbb{A}_K^{\times} \to \mathbb{C}^{\times}$ be a continuous group homomorphism (no invariance under $K^{\times}$ is assumed), and let $w$ be an infinite place of $K$ which is complex. Then there exist $u \in \mathbb{C}$ and $k \in \mathbb{Z}$ such that the predicate `IsArchCompAt K μ w u k` holds, i.e. such that for every unit $x$ of the completion $K_w$ one has
--   $$\mu_w(x) = \|x\|^{\,m_w u}\left(\frac{e_w(x)}{\|x\|}\right)^{k},$$
--   where $\mu_w =$ `archLocalChar μ w` is the composite of $\mu$ with the homomorphism `archUnitHom w` placing a unit of $K_w$ at the place $w$ and $1$ elsewhere, $e_w : K_w \to \mathbb{C}$ is the embedding `extensionEmbedding w` of the completion, $\|x\|$ is the norm of $x$ in $K_w$ viewed as a complex number, and $m_w$ is the multiplicity of $w$ (equal to $2$ at a complex place), the equality being one of complex numbers.
--
--   This is the classical classification of the continuous quasi-characters of $\mathbb{C}^{\times}$, namely $z \mapsto |z|^{2u}(z/|z|)^{k}$, applied to the local component at a complex place of a continuous idele class character. It supplies the archimedean data entering the local functional equations of Tate's global zeta integrals and the archimedean parameters used in the converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ u : ℂ, ∃ k : ℤ, IsArchCompAt K μ w u k := by sorry
