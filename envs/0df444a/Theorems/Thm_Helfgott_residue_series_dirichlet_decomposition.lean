-- Prove2me | Theorems.Thm_Helfgott_residue_series_dirichlet_decomposition
-- name    : Helfgott.residue_series_dirichlet_decomposition
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T05:42:00.502328+00:00
-- url     : https://prove2.me/theorems/52b23ddc-0b96-4654-ad51-5635e2f7c2ce
-- title:
--   Exact coprime residue-series reconstruction from complete Dirichlet character twists
-- statement:
--   Let $q>0$ be natural, let $b$ be an invertible residue modulo $q$, and let $(c_n)$ be an absolutely summable complex sequence. Summing over all complex Dirichlet characters modulo $q$, one has
--
--   $$\sum_{\substack{n\ge0\\n\equiv b\pmod q}}c_n
--   =\frac1{\varphi(q)}\sum_{\chi\bmod q}\chi(b^{-1})
--   \sum_{n\ge0}\chi(n)c_n.$$
--
--   Every twisted series converges absolutely. The identity supplies the exact character interface for complete smoothed prime sums in coprime arithmetic progressions, with all infinite tails retained. It assumes no numerical estimate on primes or L-functions.
-- source:
--   Standard Dirichlet character orthogonality, using Mathlib’s complete Orthogonality and Bounds theorems (Michael Stoll). Applied to the character analysis in H. A. Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Written by Codex.

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Basic
open Finset
open scoped BigOperators

namespace Helfgott

theorem residue_series_dirichlet_decomposition (q : ℕ) (hq : 0<q)
    (b : ZMod q) (hb : IsUnit b) (c : ℕ → ℂ) (hc : Summable c) :
    (∑' n : ℕ,if (n : ZMod q)=b then c n else 0) =
      (Nat.totient q : ℂ)⁻¹*(∑ χ : DirichletCharacter ℂ q,
        χ b⁻¹*(∑' n : ℕ,χ (n : ZMod q)*c n)) := by sorry

end Helfgott
