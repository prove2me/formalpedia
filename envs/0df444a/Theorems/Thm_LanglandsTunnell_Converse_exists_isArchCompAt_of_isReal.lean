-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
-- name    : LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/c6ef4c9d-52e8-53e2-8996-0d5ed3f3f708
-- title:
--   Local component of an idele character at a real place
-- statement:
--   Let $K$ be a number field, let $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a continuous group homomorphism from the units of the adele ring of $K$ (no invariance under $K^\times$ is assumed), and let $w$ be an infinite place of $K$ which is real. Then there exist a complex number $u$ and an element $a$ of $\mathbb{Z}/2$ such that the predicate `IsArchCompAt K μ w u ((a.val : ℕ) : ℤ)` holds, that is: for every unit $x$ of the completion $K_w$, the value of the local component `archLocalChar μ w` at $x$ — the composite of $\mu$ with the homomorphism `archUnitHom w` embedding $K_w^\times$ into the idele group at the place $w$ — satisfies
--   $$\mu_w(x) = \|x\|^{\,m_w u}\left(\frac{e_w(x)}{\|x\|}\right)^{\varepsilon},$$
--   where $e_w =$ `extensionEmbedding w` is the canonical embedding $K_w \to \mathbb{C}$, $\|{\cdot}\|$ is the norm on $K_w$ viewed in $\mathbb{C}$, $m_w$ is the multiplicity `w.mult` of $w$ (here $1$, as $w$ is real), and $\varepsilon \in \{0,1\}$ is the integer representative `a.val` of $a$; the first power is a complex power and the second an integer power.
--
--   This is the classical description of the continuous quasi-characters of $\mathbb{R}^\times$, namely $x \mapsto |x|^{u}\operatorname{sgn}(x)^{\varepsilon}$, transported to the local component at a real place of a continuous character of the idele class group. It supplies the archimedean local data used in the Tate-theoretic analysis of such characters, and is cited in the treatment of the archimedean exponents attached to Hecke eigensystems and in the determination of local components of characters of finite order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ u : ℂ, ∃ a : ZMod 2, IsArchCompAt K μ w u ((a.val : ℕ) : ℤ) := by sorry
