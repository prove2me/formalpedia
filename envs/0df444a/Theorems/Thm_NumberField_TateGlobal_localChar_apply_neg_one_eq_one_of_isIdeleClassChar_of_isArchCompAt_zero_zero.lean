-- Prove2me | Theorems.Thm_NumberField_TateGlobal_localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero
-- name    : NumberField.TateGlobal.localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/77d10a1d-64f3-5676-9c49-81717818cfeb
-- title:
--   Idele class characters of ℚ: local component at v is 1 on -1
-- statement:
--   Let $\sigma\colon (\mathbf{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathbb{Q}$ (formed over $\mathcal{O}_{\mathbb{Q}}$) which is an idele class character, that is, $\sigma(u) = 1$ for the image of every $u \in \mathbb{Q}^\times$ under the diagonal embedding of $\mathbb{Q}$ into the adeles, and assume $\sigma$ continuous. Let $v$ be a nonzero prime ideal of $\mathcal{O}_{\mathbb{Q}}$. Assume that $\sigma$ is unramified at every $w \neq v$, in the sense that for each such $w$ and each unit $t$ of the completion $\mathbb{Q}_w$ with both $t$ and $t^{-1}$ in the valuation ring, the local character `localChar` $\sigma$ at $w$ — the composite of $t \mapsto$ (the idele with entry $t$ at $w$ and $1$ elsewhere, and $1$ at the infinite component) with $\sigma$ — takes the value $1$ at $t$. Assume also that at every real infinite place $w$ of $\mathbb{Q}$ the archimedean component of $\sigma$ has type $(u,a) = (0,0)$, i.e. $\sigma$ evaluated on the idele supported at $w$ with entry $x$ equals $\|x\|^{w.\mathrm{mult}\cdot 0}\,(\iota_w(x)/\|x\|)^{0}$ for all $x \in (\mathbb{Q}_w)^\times$. Then `localChar` $\sigma$ $v$ evaluated at the unit $-1$ of $\mathbb{Q}_v$ equals $1$.
--
--   This is the normalisation statement that a continuous idele class character of $\mathbb{Q}$ which is unramified outside a single finite place $v$ and of trivial type at the real place is trivial on $-1$ in its $v$-component; it is used in the Langlands–Tunnell converse-theorem part of the development, in the construction and functional-equation bookkeeping for the cubic induction data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

theorem NumberField.TateGlobal.localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsIdeleClassChar (𝓞 ℚ) ℚ σ) (hσc : Continuous σ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → IsUnramifiedCharAt σ w)
    (harch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w 0 0) :
    localChar σ v (-1) = 1 := by sorry
