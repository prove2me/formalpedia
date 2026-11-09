-- Prove2me | Theorems.Thm_OCTKernel_Main_lemma_3_2
-- name    : OCTKernel.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:08.829119+00:00
-- url     : https://prove2.me/theorems/a5453ed5-fdd5-4f4d-91b7-d25cbf3f0cfa
-- title:
--   Lemma 3.2 — Wronskian criterion
-- statement:
--   Let $p$ be prime, $s\ge1$, and let $f_1,\ldots,f_s\in\mathbb F_p[X]$ have degrees at most $d<p$. Then
--
--   $$f_1,\ldots,f_s\text{ are linearly independent over }\mathbb F_p\quad\Longleftrightarrow\quad\operatorname{Wr}(f_1,\ldots,f_s)\ne0.$$
--
--   This criterion supplies the characteristic-sensitive polynomial independence test used by the multiplicity bound.
--
--   Differences from the source:
--   - encoding: finite labelled ground sets and one-based indices → Fin n and zero-based indices; reason: Relabelling preserves every finite instance and every rank, cut and dimension.
-- source:
--   Tomohiro Koana, Soh Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, STOC 2027 submission #810 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/810.pdf, SHA-256 043624e22f147583799f7dcc844cebbd4644ecdc53a42543f708cda5c38c6b72, Lemma 3.2, p. 8.

import Definitions.Def_OCTKernel_Main_Polynomials

set_option autoImplicit false

namespace OCTKernel.Main

theorem lemma_3_2 (p s d : ℕ) [Fact p.Prime] (hs : 1 ≤ s) (hd : d < p)
    (f : Fin s → Polynomial (ZMod p)) (hf : ∀ i, (f i).degree ≤ (d : WithBot ℕ)) :
    LinearIndependent (ZMod p) f ↔ wronskian f ≠ 0 := by sorry

end OCTKernel.Main
