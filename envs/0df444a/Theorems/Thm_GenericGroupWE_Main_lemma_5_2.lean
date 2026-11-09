-- Prove2me | Theorems.Thm_GenericGroupWE_Main_lemma_5_2
-- name    : GenericGroupWE.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:05.049082+00:00
-- url     : https://prove2.me/theorems/445049df-9195-41e7-8d88-c9873a6ff567
-- title:
--   Lemma 5.2 — Geometric column combinations span
-- statement:
--   Let $p>2^N$ be prime and let $c_0,\ldots,c_N$ span a nonzero finite-dimensional space of dimension $\rho$. For $1\le j\le\rho$, put $d_j(t)=\sum_{i=0}^N(2^{j-1}t)^ic_i$. There is a nonzero scalar polynomial $\Delta$ such that
--
--   $$\deg\Delta\le N\rho,\qquad \Delta(t)\ne0\Longrightarrow(d_1(t),\ldots,d_\rho(t))\text{ is a basis of }\operatorname{span}\{c_i\}.$$
--
--   This is the geometric spanning family used to select a sample of the weighted stack.
--
--   Differences from the source:
--   - encoding: finite indexed families and field residues → Fin-indexed families and ZMod prime fields; reason: zero-based indices and explicit finite carriers change no mathematical instance
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Lemma 5.2, PDF p. 17 (printed p. 16).

import Mathlib

namespace GenericGroupWE.Main
open scoped BigOperators

theorem lemma_5_2 (p N : ℕ) [Fact p.Prime] (hp : 2^N < p)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (c : Fin (N + 1) → V)
    (hpos : 0 < Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))) :
    let ρ := Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range c))
    ∃ Δ : Polynomial (ZMod p), Δ ≠ 0 ∧ Δ.natDegree ≤ N * ρ ∧
      ∀ t : ZMod p, Δ.eval t ≠ 0 →
        let ds := fun j : Fin ρ => ∑ i : Fin (N+1),
          ((((2 : ZMod p)^j.val) * t)^i.val) • c i
        LinearIndependent (ZMod p) ds ∧
          Submodule.span (ZMod p) (Set.range ds) = Submodule.span (ZMod p) (Set.range c) := by sorry

end GenericGroupWE.Main
