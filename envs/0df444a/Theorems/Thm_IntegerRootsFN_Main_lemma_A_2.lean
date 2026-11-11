-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_A_2
-- name    : IntegerRootsFN.Main.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:45.748129+00:00
-- url     : https://prove2.me/theorems/249dd3b3-4df1-4224-85bd-8e3961e2536f
-- title:
--   Lemma A.2 — both Graeffe-test alternatives and bit cost
-- statement:
--   Let $f\in\mathbb Z[x]$ satisfy the standing degree and strict height promises for $n,b\ge1$. Put $d=\min(n,b)$ and let $g$ be its actual top-coefficient truncation. For every integer center $m$ and integer radius $r\ge1$, Test is the coefficient-defined Graeffe test of p.12. It satisfies both implications:
--
--   $$\operatorname{Test}(m,r)=\mathrm{empty}\ \Longrightarrow\ \forall\alpha:\ g(\alpha)=0\Rightarrow|\alpha-m|>r,$$
--   $$\operatorname{Test}(m,r)\ne\mathrm{empty}\ \Longrightarrow\ \exists\alpha:\ g(\alpha)=0\ \land\ |\alpha-m|\le2r.$$
--
--   A single deterministic machine computes this test in $\widetilde O(d^2b)$ bit steps whenever $|m|\le2^b$ and $1\le r\le2^b+2$. Only this time clause needs the extra center and radius size bounds. The machine receives the already formed $g$ and its $d,b$ header, followed by signed binary $m,r$; the main theorem separately charges reading and truncating $f$. Log factors involve only $d,b$ and are uniform. The test output is one actual bit, with true denoting empty.
--
--   In particular $d=1$ performs zero Graeffe steps, and the complement branch is retained when the constant coefficient vanishes.
--
--   Differences from the source:
--   - encoding: the test uses the already formed g → machine input contains the dense truncated g, d,b, then m,r; time is measured on that input; reason: reading the full n-degree f here would contradict the source subroutine bound; the main theorem pays nb
--   - encoding: uniform soft-O bit-operation bounds → one finite deterministic multitape machine and positive global C with fixed natural exponents k,l before all varying inputs, bounded by CF(1+log₂(n+1))^k(1+log₂(b+1))^l; reason: shifted logarithms cover the small inputs without changing the allowed polynomial or logarithmic scope; finite initially blank work tapes prohibit advice or assigned costs
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 12, Lemma A.2

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem lemma_A_2 :
    (∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∀ m r : ℤ, 1 ≤ r →
        (testEmpty (truncate f n b) (min n b) m r = true →
          ∀ α : ℂ, (complexify (truncate f n b)).IsRoot α → (r : ℝ) < ‖α - (m : ℂ)‖) ∧
        (testEmpty (truncate f n b) (min n b) m r = false →
          ∃ α : ℂ, (complexify (truncate f n b)).IsRoot α ∧ ‖α - (m : ℂ)‖ ≤ 2 * r)) ∧
    (∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∀ m r : ℤ, |m| ≤ (2 : ℤ) ^ b → 1 ≤ r → r ≤ (2 : ℤ) ^ b + 2 →
      Runs M (testInputWord (truncate f n b) (min n b) b m r)
        [some (testEmpty (truncate f n b) (min n b) m r)]
        (softBound C k l (min n b) b ((min n b : ℕ) ^ 2 * (b : ℝ)))) := by sorry

end IntegerRootsFN.Main
