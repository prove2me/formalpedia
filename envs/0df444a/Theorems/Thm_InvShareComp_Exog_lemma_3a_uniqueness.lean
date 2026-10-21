-- Prove2me | Theorems.Thm_InvShareComp_Exog_lemma_3a_uniqueness
-- name    : InvShareComp.Exog.lemma_3a_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:58.335729+00:00
-- url     : https://prove2.me/theorems/627c9e26-d27b-46fb-b442-5043dc750d8b
-- title:
--   Lemma 3(a), uniqueness, p. 13 (PDF 13) — a symmetric sharing equilibrium has service level ŝ(t, I)
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, inventories $I_1=I_2=I\in[0,1]$ and a non-moot transfer price $t\in[0,\bar c-\delta]$: if $(s,s)$ is a symmetric equilibrium of the sharing subgame, then
--   $$s=\hat s(t,I)=\frac{\beta(p\mu-A-B)}{2k},$$
--   with $A$ and $B$ the region integrals of Lemma 3(a).
--
--   This pins down every symmetric equilibrium of the sharing subgame, which is how Proposition 2's comparisons over equilibria reduce to comparisons of closed forms.
--
--   **Formalization Note.** Only the uniqueness half of Lemma 3(a) is stated. The existence half is not posed: the paper's proof checks the second-order condition only at the candidate, and a uniform i.i.d. instance ($p=1$, $\bar c=0.951$, $\delta=0.0108$, $c=0.151$, $I=0.193$, $k=0.368$, $\beta=1.839$, $t=0.245$) has a profitable deviation from $(\hat s,\hat s)$. Deviations keep both deterministic demands non-negative. The bound $\beta\le\bar\beta$ is not assumed.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 13 (PDF 13), Lemma 3(a), equation (4); proof in Online Appendix p. 7 (PDF 39)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem lemma_3a_uniqueness (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) (s : ℝ) :
    IsSymEqShare P ν t I s → s = sHat P ν t I := by sorry

end InvShareComp.Exog
