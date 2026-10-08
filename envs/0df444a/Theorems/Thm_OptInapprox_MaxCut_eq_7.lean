-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_eq_7
-- name    : OptInapprox.MaxCut.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:43.316083+00:00
-- url     : https://prove2.me/theorems/bc1a41b7-8973-4006-8114-e63c3f71e563
-- title:
--   (7), §8.3, p. 19 — ĝ_v(S) = E_w[f̂_w(σ⁻¹(S))] and Inf_j^{≤k}(g_v) ≤ E_w[Inf^{≤k}_{σ⁻¹(j)}(f_w)]
-- statement:
--   Let $\mathcal L$ be a Unique Label Cover instance, $f_w:\{-1,1\}^M\to\{-1,1\}$ ($w\in W$) any proof, and $v\in V$. With $g_v(z)=\mathbf E_{w\sim v}[f_w(z\circ\sigma_{v,w})]$:
--
--   1. for every $S\subseteq[M]$, $\widehat{g_v}(S)=\mathbf E_w\big[\widehat{f_w}(\sigma_{v,w}^{-1}(S))\big]$;
--   2. for every $k$ and every $j\in[M]$,
--   $$\mathrm{Inf}^{\le k}_j(g_v)\ \le\ \mathbf E_w\Big[\mathrm{Inf}^{\le k}_{\sigma_{v,w}^{-1}(j)}(f_w)\Big].$$
--
--   Here $\mathbf E_w$ is the average over the neighbours $w$ of $v$. The inequality is the chain (7) without its first link $\delta\le\mathrm{Inf}_j^{\le k}(g_v)$, which holds for "good" $v$; it transfers a large low-degree influence of $g_v$ to the Long Codes of $v$'s neighbours.
--
--   **Formalization Note.** The chain is stated for every $v$ and $j$. If $v$ has no neighbours, both sides are $0$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 19, §8.3 Soundness, eq. (7)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

namespace OptInapprox.MaxCut

theorem eq_7 (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (v : Fin L.nV) :
    (∀ S : Finset (Fin L.M), fourier (gv L F v) S =
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        fourier (fun x => pm (F w x)) (S.map (L.σ v w).symm.toEmbedding)) ∧
    ∀ (k : ℕ) (j : Fin L.M), lowDegInf k j (gv L F v) ≤
      ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v,
        lowDegInf k ((L.σ v w).symm j) (fun x => pm (F w x)) := by sorry

end OptInapprox.MaxCut
