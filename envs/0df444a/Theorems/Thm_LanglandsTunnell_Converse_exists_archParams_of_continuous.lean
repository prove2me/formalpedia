-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_archParams_of_continuous
-- name    : LanglandsTunnell.Converse.exists_archParams_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/6b82bac3-1dd1-50a7-b02d-b26bbd1ba526
-- title:
--   Archimedean components of a continuous idele class character
-- statement:
--   Let $K$ be a number field, and let $\mu : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a continuous group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$; no invariance under $K^\times$ is assumed. The assertion is the existence of four families of parameters indexed by the infinite places of $K$: complex numbers $u_{\mathbb{R}}(w)$ and elements $a(w) \in \mathbb{Z}/2$ for each real place $w$, and complex numbers $u_{\mathbb{C}}(w)$ and integers $k(w)$ for each complex place $w$, such that the local component of $\mu$ at every infinite place is given by these parameters in the sense of the predicate `IsArchCompAt`. Explicitly, writing $\mu_w$ for `archLocalChar` $\mu$ $w$, the composite of $\mu$ with the embedding `archUnitHom` $w$ of $K_w^\times$ into the idele group at the single place $w$, $e$ for the canonical embedding `extensionEmbedding` of the completion $K_w$ into $\mathbb{C}$, and $m_w$ for the multiplicity of $w$, the conclusion is that for every $x \in K_w^\times$
--   $$\mu_w(x) = \|x\|^{m_w u(w)} \left(\frac{e(x)}{\|x\|}\right)^{c(w)},$$
--   with $\|x\|$ the norm of $x$ in $K_w$, the first power a complex power of the positive real $\|x\|$ and the second an integer power, where $(u(w), c(w)) = (u_{\mathbb{R}}(w), a(w)\bmod 2 \in \{0,1\})$ at real places and $(u(w), c(w)) = (u_{\mathbb{C}}(w), k(w))$ at complex places.
--
--   This is the classical classification of the continuous quasi-characters of the archimedean local fields $\mathbb{R}^\times$ and $\mathbb{C}^\times$, applied simultaneously to all infinite places of $K$ to extract the archimedean parameters of an idele character. The parameters so produced feed the archimedean analysis of the converse-theorem construction, being used in the estimates for cusp synthesis (growth exponents, local majorants, bounds on Siegel sets, and the $L^p$ bounds on translated sums).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_archParams_of_continuous.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_archParams_of_continuous (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    ∃ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
      (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
      (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
      (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
      (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) ∧
      (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) := by sorry
