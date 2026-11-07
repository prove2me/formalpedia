-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_4_4
-- name    : MinBisectFPT.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:05.003219+00:00
-- url     : https://prove2.me/theorems/1ba78da7-4da3-42ff-8309-31d7f1d33a34
-- title:
--   Lemma 4.4 — $\Psi(U)\ne0$ forces a connected set with small cut
-- statement:
--   Under the standing assumptions of §4, let $U\subseteq\beta$ be nonempty with $\Psi(U)\ne0$. Then $|U|\le q$, and there is a set $Y\subseteq\gamma(t)$ with $Y\cap\beta=U$ such that $|\delta(Y)|\le k$ and $H[Y]$ is connected.
--
--   Cuts and connectivity are taken in $H=G_t$. So every nonempty $U$ with $\Psi(U)\ne0$ is a candidate, and only candidates need to be listed.
--
--   Differences from the source:
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
--   - encoding: $\exp$, $\log$ with any $N$ such that $f^{N+1}=0$ → `expN`, `logN` with $N=q+k$; reason: $J_t^{q+k+1}=0$ and the series do not depend on $N$ (p.10)
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.4, p.13

import Mathlib
import Definitions.Def_MinBisectFPT_NodeCtx

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 4.4.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.4, p.13: "Let U ⊆ β be nonempty with Ψ(U) ≠ 0. Then (i) |U| ≤ q, and there
is a set Y ⊆ γ(t) with Y ∩ β = U such that (ii) |δ(Y)| ≤ k, and (iii) H[Y] is connected." -/
theorem lemma_4_4 {n : ℕ} (ctx : NodeCtx n) (U : Finset (Fin n)) (hU : U ⊆ ctx.β)
    (hne : U.Nonempty) (hPsi : ctx.Psi U ≠ 0) :
    U.card ≤ ctx.q ∧ ∃ Y, Y ⊆ ctx.γ ∧ Y ∩ ctx.β = U ∧ cutSize ctx.H Y ≤ ctx.k ∧
      (ctx.H.induce (Y : Set (Fin n))).Connected := by sorry

end MinBisectFPT
