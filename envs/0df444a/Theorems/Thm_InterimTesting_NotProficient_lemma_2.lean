-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_2
-- name    : InterimTesting.NotProficient.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:49.612898+00:00
-- url     : https://prove2.me/theorems/6ee1b9fa-b2c8-44eb-8ba8-178a55c01ed6
-- title:
--   Lemma 2 (S0 = N), p. 13 (PDF 13) — under (14), first-period effort is 1 iff π ≥ 𝒯0(N) = 1/(µ(1−µ)A(A+B))
-- statement:
--   Suppose condition (14) holds,
--   $$\frac{(1-\phi_{P|P})\phi_{P|N}}{\phi_{P|P}-\phi_{P|N}}\le\frac{(1-(A+B))B}{A},$$
--   or the district uses the interim assessment (the case $\phi_{P|P}=1$, $\phi_{P|N}=0$, where (14) holds automatically). For a school starting not proficient and every incentive $\pi\ge0$, the teachers' optimal first-period effort is
--   $$e_0^*(N)=\begin{cases}0,&\pi<\mathcal T_0(N),\\1,&\mathcal T_0(N)\le\pi,\end{cases}\qquad \mathcal T_0(N)=\frac{1}{\mu(1-\mu)A(A+B)}.$$
--
--   For a school that starts behind, the first-period threshold does not depend on the accuracy of the midyear information.
--
--   **Formalization Note** Only the $S_0=N$ half of the expanded Lemma 2, (A55) and (A57), is stated; the $S_0=P$ threshold (A56), (A58) is not used by Proposition 1. The hypothesis is `zI = true ∨ Cond14 θ`.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. 13 (PDF 13), Lemma 2, (14); expanded p. A10 (PDF 36), (A54), (A55), (A57)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma 2, `S0 = N`, p. 13 (expanded (A55), (A57), p. A10): under (14) — automatic under the
interim assessment, the case `ϕ_{P|P} = 1`, `ϕ_{P|N} = 0` — the optimal first-period effort is
`1` if `π ≥ 𝒯0(N) = 1/(μ(1 − μ)A(A + B))` and `0` otherwise. -/
theorem lemma_2 (θ : Params) (hθ : θ.Standing) (zI : Bool) (h14 : zI = true ∨ Cond14 θ)
    (π : ℝ) (hπ : 0 ≤ π) :
    e0Star θ zI .N π = if T0N θ ≤ π then 1 else 0 := by sorry

end InterimTesting.NotProficient
