-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_lemma_2_1
-- name    : OptimalAgnosticPAC.Learner.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:33.288023+00:00
-- url     : https://prove2.me/theorems/b1141ad2-dad5-4523-8d0a-457329c1ecc5
-- title:
--   Lemma 2.1: class dependent edge isoperimetry on the Boolean cube
-- statement:
--   Let $P$ be a nonempty finite coordinate set and $\mathcal F\subseteq V_P=\{-1,+1\}^P$ nonempty. There are weights $w_{v,p}\in[0,1]$, fixed simultaneously for all $v\in V_P$ and $p\in P$, such that for every $v$, every $p$ and every $D\subseteq P$,
--   $$w_{v,p}+w_{v^{\oplus p},p}=1,\tag{5}$$
--   $$\sum_{p\in D}w_{v,p}\le\rho_{\mathcal F}(v)+\mathfrak R_D(\mathcal F).\tag{6}$$
--   Consequently, for every $U\subseteq V_P$,
--   $$|E_U|\le\sum_{v\in U}\bigl(\rho_{\mathcal F}(v)+\mathfrak R_{D_U(v)}(\mathcal F)\bigr).\tag{7}$$
--
--   This inequality ties induced edge counts on the cube to the distance from $\mathcal F$ and to projected widths. The coefficient one on $\rho_{\mathcal F}(v)$ is what later yields coefficient one on the optimal risk.
--
--   Differences from the source:
--   - encoding: V_P = {−1,+1}^P with P a nonempty finite set → P : Type with Fintype and Nonempty, labelings P → Bool with true for +1, signed values through sgn; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - encoding: E_U is a set of unordered cube edges → inducedEdges of cubeGraph P, a Finset of Sym2; reason: each edge is one element, so it is counted once
--   - generalization: F is the fixed nonempty F with VC(F) ≤ d of §2 → F is any nonempty subset of the cube; reason: the lemma's statement and proof do not involve d; Remark 2.2 uses it for any F
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §2, Lemma 2.1, PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Lemma 2.1, PDF p. 4: one family of weights `w` serves (5) and (6) for all `v`, `p`, `D` at
once, and (7) holds for every `U`. -/
theorem lemma_2_1 {P : Type} [Fintype P] [Nonempty P] (F : Set (P → Bool)) (hF : F.Nonempty) :
    (∃ w : (P → Bool) → P → ℝ,
      (∀ v p, w v p ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ v p, w v p + w (flipAt v p) p = 1) ∧
      (∀ (v : P → Bool) (D : Finset P), ∑ p ∈ D, w v p ≤ (rho F v : ℝ) + width F D)) ∧
    (∀ U : Finset (P → Bool),
      ((inducedEdges (cubeGraph P) U).card : ℝ) ≤
        ∑ v ∈ U, ((rho F v : ℝ) + width F (dirs U v))) := by sorry

end OptimalAgnosticPAC.Learner
