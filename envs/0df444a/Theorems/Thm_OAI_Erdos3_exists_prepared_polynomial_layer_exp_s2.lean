-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_prepared_polynomial_layer_exp_s2
-- name    : OAI.Erdos3.exists_prepared_polynomial_layer_exp_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:18:45.863476+00:00
-- url     : https://prove2.me/theorems/55cb9c35-e873-4709-a4e1-8dfbc0d02292
-- title:
--   A vector polynomial of degree j+1 restricted to a residue box slice splits into a prepared rank family, an integer polynomial, a constant and a small error
-- statement:
--   Let $I, J$ be finite types (in `Type`) with decidable equality, $j, R$ natural numbers, and $p, \delta$ reals. Let $P$ be a vector polynomial in `VectorPolynomial I ℝ (J → ℝ)` (that is, $\mathbb{R}[I] \otimes (J \to \mathbb{R})$, defined by OpenAI) of total degree at most $j+1$ (every coefficient of a monomial of total degree greater than $j+1$ vanishes). Assume $p \ge 0$, $1 \le R \le e^p$, $\delta > 0$. Let $N : I \to \mathbb{N}$ and $f : \prod_i \operatorname{Fin} N(i) \to \mathbb{R}$. Put $D = \#J$, $T = (j+1) D$, $M$ = `preparationCoordinateCap (j+1) D T` $= D(T+1)^{j+1} + D + T + 1$, $\mathrm{share} = \delta / (T M + 1)$, and $\mathrm{budget} = (p+2)^{\beta + 7}$ where $\beta$ = `budgetDepthExponent 38 (j+1)` (OpenAI's recursion $\beta_0 = 1$, $\beta_{d+1} = 38(\beta_d + 2)$). Assume $M \le p$, $j + 1 \le p$, $\#I \le p$, $T + 1 \le p$, $\mathrm{share}^{-1} \le e^p$, and $e^{\mathrm{budget}} \le N(i)$ for all $i$.
--
--   Then there exist a natural number $q$, a residue box slice $S$ of $\prod_i [0, N(i))$ with step $q$ (OpenAI's `ResidueBoxSlice N q`: starts $a_i$ and lengths $\ell_i$ with $a_i + q t < N(i)$ for all $t < \ell_i$; its point at $x \in \prod_i \operatorname{Fin} \ell_i$ is $S.\mathrm{point}(x)_i = a_i + q x_i$), a `RankPreparationFamily I J (j+1)` $L$ (a family of $j+1$ rank preparation layers, defined by OpenAI), integer polynomials $\mathrm{ip}_k \in \mathbb{Z}[I]$ for $k \in J$, reals $c_k$ for $k \in J$, and $\mathrm{err} : \prod_i \operatorname{Fin} \ell_i \to J \to \mathbb{R}$ such that:
--   - $\sum_{u} \operatorname{rank}(L_u) \le T$, where the rank of a layer is the real dimension of its rational space `(L u).space`; `L.Sized D T` (layer $u$ has at most $D(T+1)^{j - u}$ coordinates, at most $D + T$ columns and at most $T$ rows); and `L.PreparedHeights p R` (each layer $u$ is valid in OpenAI's sense at degree $u+1$ with height `preparationHeight p (j - u)` and bound $R$);
--   - for each layer $u$, `HasLayerSamplingRank (u+1) ℓ R (L u).space (L u).poly` holds (with the slice lengths $\ell_i$ as scales);
--   - $0 < q \le e^{\mathrm{budget}}$; for every $i$, $\ell_i > 0$ and $N(i) \le e^{\mathrm{budget}} \ell_i$;
--   - $\mathbb{E}_{x \in \prod_i \operatorname{Fin} N(i)} f(x) \le \mathbb{E}_{x \in \prod_i \operatorname{Fin} \ell_i} f(S.\mathrm{point}(x))$;
--   - each $\mathrm{ip}_k$ has total degree at most $j+1$, and $|\mathrm{err}(x, k)| \le \delta$ for all $x, k$;
--   - for all $x \in \prod_i \operatorname{Fin} \ell_i$ and $k \in J$: $P(S.\mathrm{point}(x))_k = L.\mathrm{value}(x)_k + \mathrm{ip}_k(x) + c_k + \mathrm{err}(x, k)$, where $P$ is evaluated at the real point $(S.\mathrm{point}(x)_i)_i$, $\mathrm{ip}_k$ at the integer point $(x_i)_i$, and $L.\mathrm{value}(x) = \sum_u$ `(L u).value` $x$ (each layer's polynomial evaluated at $(x_i)_i$, with coordinates summed into $J$ according to the layer's labels).
--
--   Lean: `OAI.Erdos3.exists_prepared_polynomial_layer_exp_s2`, which states OpenAI's `OAI.Erdos3.exists_prepared_polynomial_layer_exp` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PreparedPolynomialIdentity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B137` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PreparedPolynomialIdentity.lean (declaration OAI.Erdos3.exists_prepared_polynomial_layer_exp)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B137

section

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem exists_prepared_polynomial_layer_exp_s2 {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    (M : ℝ) ≤ p → ((j + 1 : ℕ) : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ p →
    (T : ℝ) + 1 ≤ p → share⁻¹ ≤ Real.exp p → (∀ i, Real.exp budget ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ (∀ x k, |err x k| ≤ δ) ∧
      ∀ x k, eval (fun i => ((S.point x i).val : ℝ)) P k =
        L.value (fun i => ((x i).val : ℝ)) k +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip k) : ℝ) + c k + err x k := by
  sorry

end Erdos3

end

end OAI
end
