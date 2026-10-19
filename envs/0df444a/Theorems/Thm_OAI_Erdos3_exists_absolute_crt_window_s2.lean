-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_absolute_crt_window_s2
-- name    : OAI.Erdos3.exists_absolute_crt_window_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:02.218849+00:00
-- url     : https://prove2.me/theorems/90f8d60c-a07c-4f8f-b96c-4078b443c648
-- title:
--   An AP-free dense set in a box of distinct primes correlates with a positive cyclic niltest times a CRT window patch
-- statement:
--   Let $J$ be a finite nonempty type with decidable equality, and let $k \ge 3$ be a natural number. Then there exist natural numbers $C_{sc} \ge 2$, $C \ge 2$ with $C_{sc} < C$, a natural number $C_{\mathrm{window}} \ge 2$, and a real number $\xi > 0$ with the following property.
--
--   Let $N : J \to \mathbb{N}$ be such that every $N_j$ is prime (in particular nonzero, and the product $\prod_j N_j$ is nonzero) and $N$ is injective. Let $f : \prod_j \mathbb{Z}/N_j \to \mathbb{R}$, and let $\alpha, p$ be real numbers with $\alpha > 0$, $p \ge 2$, $\log(1/\alpha) \le p$, and $e^{(p+2)^C} \le N_j$ for every $j$. Suppose $0 \le f(u) \le 1$ for all $u$, the uniform average of $f$ over $\prod_j \mathbb{Z}/N_j$ equals $\alpha$, and the set of integer vectors $\{(\mathrm{val}(u_j))_j : f(u) \ne 0\}$ (each residue represented in $[0, N_j)$) is `IntegerVectorAPFree` of length $k$ (for all $a, d \in \mathbb{Z}^J$ with $d \ne 0$, some point $a + i d$ with $0 \le i < k$ lies outside the set). Write $\Phi : \mathbb{Z}/\prod_j N_j \to \prod_j \mathbb{Z}/N_j$ for the Chinese remainder isomorphism (`ZMod.prodEquivPi`, using that distinct primes are pairwise coprime).
--
--   Then there exist $T : \mathbb{Z}/\prod_j N_j \to \mathbb{R}$ and a `RepresentativeWindow` $w$ (defined by OpenAI: a center and a function $[0,1]$-valued, supported in $(0, 1)$ within distance $1/4$ of the center, and Lipschitz with constant `w.lip`) such that:
--
--   - `PositiveCyclicNiltest (k - 2) (∏ j, N j) ((p + 2)^Csc) T` holds (a predicate defined by OpenAI: $T$ is given by a positive niltest of degree $k - 2$ on the cyclic group of order $\prod_j N_j$ with complexity at most $(p+2)^{C_{sc}}$);
--   - $\log(2 + \texttt{w.lip}) \le (p + 2)^{C_{\mathrm{window}}}$;
--   - $$e^{-(p+2)^{C_{\mathrm{window}}}} \le \mathbb{E}_{u \in \prod_j \mathbb{Z}/N_j}\ \bigl(f(u) - (1 + \xi)\alpha\bigr)\cdot T(\Phi^{-1}(u))\cdot \texttt{(w.crtPatch N hN (k - 2) _).value}\bigl(j \mapsto \mathrm{val}(u_j)\bigr),$$
--     where `w.crtPatch N hN (k - 2) _` is a `PolynomialPatch J (k - 2) 1` defined by OpenAI whose value at an integer vector $v$ is $w\bigl(\mathrm{val}(\Phi^{-1}(v \bmod N)) / \prod_j N_j\bigr)$.
--
--   Lean: `OAI.Erdos3.exists_absolute_crt_window_s2`, which states OpenAI's `OAI.Erdos3.exists_absolute_crt_window` (in `lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B035`, `OAIE3v2B037`, `OAIE3v2B142` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean (declaration OAI.Erdos3.exists_absolute_crt_window)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B142

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_absolute_crt_window_s2 {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Csc : ℕ, 2 ≤ Csc ∧ ∃ C : ℕ, 2 ≤ C ∧ Csc < C ∧
      ∃ Cwindow : ℕ, 2 ≤ Cwindow ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ u, 0 ≤ f u ∧ f u ≤ 1) → (𝔼 u, f u) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        let hN := distinct_prime_moduli_coprime N hprime hinj
        ∃ (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow),
          PositiveCyclicNiltest.{0} (k - 2) (∏ j, N j) ((p + 2) ^ Csc) T ∧
          Real.log (2 + (w.lip : ℝ)) ≤ (p + 2) ^ Cwindow ∧
          Real.exp (-((p + 2) ^ Cwindow)) ≤
            𝔼 u : (j : J) → ZMod (N j),
              ((f u - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm u)) *
                (w.crtPatch N hN (k - 2) (by omega)).value (fun j => ((u j).val : ℝ)) := by
  sorry

end Erdos3

end

end OAI
end
