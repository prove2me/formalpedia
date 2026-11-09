-- Prove2me | Theorems.Thm_OCTKernel_Main_lemma_3_4
-- name    : OCTKernel.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:14.936204+00:00
-- url     : https://prove2.me/theorems/1860de03-99e7-4822-a9fd-4da1117863f7
-- title:
--   Lemma 3.4 — Independence from high-multiplicity roots
-- statement:
--   Let $p$ be prime and let $n,t,K\ge1$ satisfy $K>n(t+n-1)$ and $K+t-1<p$. Let $\alpha_1,\ldots,\alpha_n\in\mathbb F_p$ be distinct. For each $i$, choose a nonzero polynomial $P_i=(X-\alpha_i)^KQ_i$ with $\deg Q_i<t$. Then
--
--   $$P_1,\ldots,P_n\text{ are linearly independent over }\mathbb F_p.$$
--
--   This gives independent polynomial spaces attached to distinct left vertices.
--
--   Differences from the source:
--   - encoding: finite labelled ground sets and one-based indices → Fin n and zero-based indices; reason: Relabelling preserves every finite instance and every rank, cut and dimension.
-- source:
--   Tomohiro Koana, Soh Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, STOC 2027 submission #810 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/810.pdf, SHA-256 043624e22f147583799f7dcc844cebbd4644ecdc53a42543f708cda5c38c6b72, Lemma 3.4, p. 8.

import Definitions.Def_OCTKernel_Main_Polynomials

set_option autoImplicit false

namespace OCTKernel.Main

theorem lemma_3_4 (p n t K : ℕ) [Fact p.Prime]
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hlarge : n * (t + n - 1) < K) (hchar : K + t - 1 < p)
    (α : Fin n → ZMod p) (hα : Function.Injective α)
    (P : Fin n → Polynomial (ZMod p)) (hP : ∀ i, P i ≠ 0)
    (hform : ∀ i, ∃ Q : Polynomial (ZMod p), Q.degree < (t : WithBot ℕ) ∧
      P i = (Polynomial.X - Polynomial.C (α i)) ^ K * Q) :
    LinearIndependent (ZMod p) P := by sorry

end OCTKernel.Main
