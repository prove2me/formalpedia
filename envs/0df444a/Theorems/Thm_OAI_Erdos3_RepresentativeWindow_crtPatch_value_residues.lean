-- Prove2me | Theorems.Thm_OAI_Erdos3_RepresentativeWindow_crtPatch_value_residues
-- name    : OAI.Erdos3.RepresentativeWindow.crtPatch_value_residues
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:03:06.592261+00:00
-- url     : https://prove2.me/theorems/87bc2233-f107-4f45-9eef-caa00bb895f1
-- title:
--   The CRT patch of a representative window evaluates the window at the CRT fraction
-- statement:
--   Let $J$ be a finite type with decidable equality and $N : J\to\mathbb{N}$ with $N_j\ne 0$ for every $j$ and $\prod_{j\in J}N_j\ne 0$, and let $h_N$ be a proof that the $N_j$ are pairwise coprime. Let $w$ be a `RepresentativeWindow` (a structure bundling a real center and a $[0,1]$-valued Lipschitz function $w.\mathrm{value}:\mathbb{R}\to\mathbb{R}$ whose support lies in $(0,1)$ and within $1/4$ of the center), let $s$ be a natural number with $1\le s$, and let $u\in\prod_{j\in J}\mathbb{Z}/N_j\mathbb{Z}$. Let $r\in\{0,\dots,\prod_j N_j-1\}$ be the representative of the residue class modulo $\prod_j N_j$ that corresponds to $u$ under the Chinese remainder isomorphism (Mathlib's `ZMod.prodEquivPi N hN`). Then the value of the patch `w.crtPatch N hN s hs` (a `PolynomialPatch J s 1`, which OpenAI builds as `w.patch s hs` applied to `crtRepresentativePolynomial N hN`) at the real point $(\mathrm{val}(u_j))_{j\in J}$, where $\mathrm{val}(u_j)\in\{0,\dots,N_j-1\}$ is the least natural representative of $u_j$, equals
--   $$w.\mathrm{value}\Big(\frac{r}{\prod_{j\in J}N_j}\Big).$$
--
--   Lean: `OAI.Erdos3.RepresentativeWindow.crtPatch_value_residues` in `lean/OAI/Combinatorics/Progressions/Geometry/RepresentativeWindowTransport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/RepresentativeWindowTransport.lean#L49

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

namespace OAI

section

namespace Erdos3.RepresentativeWindow

open MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtPatch_value_residues [∀ j, NeZero (N j)] (w : RepresentativeWindow)
    (s : ℕ) (hs : 1 ≤ s) (u : (j : J) → ZMod (N j)) :
    (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) := by
  sorry

end Erdos3.RepresentativeWindow
end
end OAI
