-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_polynomial_scored_crt_representative_patch
-- name    : OAI.Erdos3.exists_polynomial_scored_crt_representative_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T15:47:42.700678+00:00
-- url     : https://prove2.me/theorems/7c2a06ed-cd77-403e-861a-a5e863b6d54f
-- title:
--   A representative-window CRT patch with polynomially bounded log-Lipschitz cost correlates
-- statement:
--   There is a natural number $C\ge2$ such that the following holds for every finite type $J$ with decidable equality, every family $N\colon J\to\mathbb N$ of nonzero, pairwise coprime moduli (with $\prod_jN_j\ne0$), every natural number $s\ge1$, every $f\colon\mathbb Z/(\prod_jN_j)\to\mathbb R$, and all reals $p,M,\sigma$: if $0\le p$, $0<M\le e^p$, $e^{-p}\le\sigma$, $|f(x)|\le M$ for all $x$, $\sigma\le\mathbb E_xf(x)$ (uniform average over $\mathbb Z/\prod N_j$), and $1/\prod_jN_j\le\sigma/(100M)$, then there is a `RepresentativeWindow` $w$ (a structure bundling a center $\in\mathbb R$ and a $[0,1]$-valued Lipschitz function on $\mathbb R$, with its Lipschitz constant, supported in $(0,1)$ within distance $1/4$ of the center) such that $\log\big(2+\mathrm{lip}\big)\le(p+2)^C$, where $\mathrm{lip}$ is the Lipschitz constant of the kernel of the patch $\mathcal P=$ `w.crtPatch N hN s hs`, and
--   $$e^{-(p+2)^C}\le\mathbb E_{u\in\prod_j\mathbb Z/N_j}\,f\big(\mathrm{CRT}^{-1}(u)\big)\,\mathcal P\big((u_j)_j\big).$$
--   Here $\mathrm{CRT}$ is Mathlib's `ZMod.prodEquivPi N hN`, $(u_j)_j$ is read as the real vector of the representatives $u_j\in\{0,\dots,N_j-1\}$, and `w.crtPatch N hN s hs` is a `PolynomialPatch J s 1` (a structure bundling slot weights at most $s$, a polynomial slot form and a `PatchKernel`, a $[0,1]$-valued Lipschitz kernel with Lipschitz constant `kernel.lip`), obtained from $w$ and the linear polynomial `crtRepresentativePolynomial N hN` that represents the CRT lift divided by $\prod_jN_j$; $\mathcal P(t)$ denotes its `value`. The order of quantifiers is: $\exists C$, then $\forall J,N,s,f,p,M,\sigma$, then $\exists w$.
--
--   Lean: `OAI.Erdos3.exists_polynomial_scored_crt_representative_patch` in `lean/OAI/Combinatorics/Progressions/Dynamics/RepresentativeWindowBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B094` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/RepresentativeWindowBudget.lean#L61

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B094

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_polynomial_scored_crt_representative_patch :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (s : ℕ) (hs : 1 ≤ s)
      (f : ZMod (∏ j, N j) → ℝ) {p M sigma : ℝ},
      0 ≤ p → 0 < M → M ≤ Real.exp p → Real.exp (-p) ≤ sigma →
      (∀ x, |f x| ≤ M) → sigma ≤ (𝔼 x, f x) →
      1 / ((∏ j, N j : ℕ) : ℝ) ≤ sigma / (100 * M) →
      ∃ w : RepresentativeWindow,
        Real.log (2 + ((w.crtPatch N hN s hs).kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          𝔼 u : (j : J) → ZMod (N j), f ((ZMod.prodEquivPi N hN).symm u) *
            (w.crtPatch N hN s hs).value (fun j => ((u j).val : ℝ)) := by
  sorry

end Erdos3
end
end OAI
