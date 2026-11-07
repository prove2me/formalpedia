-- Prove2me | Theorems.Thm_MatchVec3_lemma_4_1
-- name    : MatchVec3.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:30.66681+00:00
-- url     : https://prove2.me/theorems/3782789c-5db8-462b-991b-12758ca79e73
-- title:
--   Lemma 4.1: residue indicator with a short inner-product representation (corrected: $n\ge2$)
-- statement:
--   Let $m=p^aq^b$ and let $\alpha,\beta$ have the two-residue structure. There is a constant $d$ depending only on $m$ such that for every $n\ge2$ there is a function $\Delta:\mathbb Z^n_m\times\mathbb Z^n_m\to\mathbb F_p$ with
--
--   $$\Delta(x,y)=\begin{cases}1,&\langle x,y\rangle=\beta,\\0,&\langle x,y\rangle\in\{0,\alpha\},\end{cases}$$
--
--   an integer $R\le n^{d}$ and maps $\Phi,\Psi:\mathbb Z^n_m\to\mathbb F^R_p$ such that:
--
--   1. $\Delta(x,y)=\langle\Phi(x),\Psi(y)\rangle_{\mathbb F_p}$;
--   2. for every $h\ge1$ and all inputs $x^{(\ell)},y^{(\ell)}$, one has $\prod_{\ell=1}^h\Delta(x^{(\ell)},y^{(\ell)})=\big\langle\bigotimes_\ell\Phi(x^{(\ell)}),\bigotimes_\ell\Psi(y^{(\ell)})\big\rangle_{\mathbb F_p}$, in a space of dimension $R^h\le n^{dh}$;
--   3. for every $h\ge1$, every matrix with $(i,j)$ entry $\prod_{\ell=1}^h\Delta(x_i^{(\ell)},y_j^{(\ell)})$ has rank at most $n^{dh}$ over $\mathbb F_p$.
--
--   This low-rank test is what turns the count separation into a bound on matchings.
--
--   **Formalization Note** $\Delta$ is unconstrained where $\langle x,y\rangle\notin\{0,\alpha,\beta\}$. The tensor space is indexed by `Fin h → Fin R`.
--
--   Differences from the source:
--   - correction: R ≤ n^{d_m} with no restriction on n → n ≥ 2; reason: at n = 1 the bound says R ≤ 1, false for m = 12, α = 4, β = 6: xy = 6 at (1,6), (2,3) and xy = 0 at (2,6) rule out a rank-one form over any field
--   - generalization: "There is a prime field F_p" → F_p is ZMod p for the p of m = p^a q^b; reason: this is the field the proof constructs and the one the matching-number bound needs; it implies the page's existential
--   - encoding: d_m = O_m(1) and n^{O_m(h)} → one ∃ d after m, p, q, a, b and before n, α, β, h, serving R ≤ n^d, R^h ≤ n^(d·h) and the rank bound; reason: the O_m notation, with R^h ≤ n^{dh} following from R ≤ n^d
--   - encoding: the tensor space of dimension R^h → vectors indexed by Fin h → Fin R; reason: a space of dimension R^h with its coordinate inner product
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 4.1, p.11

import Mathlib
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_tensorVec

namespace MatchVec3

/-- **Lemma 4.1 (Residue indicator)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Lemma 4.1, p.11). Let `m = p^a q^b` and let `α, β` satisfy Lemma 2.3. There is a function
`∆ : Z_m^n × Z_m^n → F_p` with `∆(x, y) = 1` if `⟨x, y⟩ = β` and `∆(x, y) = 0` if `⟨x, y⟩ ∈ {0, α}`, and
a representation `∆(x, y) = ⟨Φ(x), Ψ(y)⟩` in dimension `R ≤ n^d`, with `d = O_m(1)`. Products of
indicator values have the tensor representation in dimension `R^h ≤ n^(O_m(h))`, and every matrix with
entries `∏_ℓ ∆(x_i^(ℓ), y_j^(ℓ))` has rank at most `n^(O_m(h))` over `F_p`.

**Formalization Note** `d` comes after `m, p, q, a, b` and before `n, α, β, h`, and the same `d` serves
all three bounds. The statement is for `n ≥ 2`: at `n = 1` the bound `R ≤ 1` is false (`m = 12`,
`α = 4`, `β = 6`). `∆` is free outside `⟨x, y⟩ ∈ {0, α, β}`. The field is `ZMod p` for the `p` of
`m = p^a q^b`. The tensor space is indexed by `Fin h → Fin R`, of dimension `R ^ h`. -/
theorem lemma_4_1 (m p q a b : ℕ) : ∃ d : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ α β : ZMod m,
    ResidueStructure m p q a b α β →
    ∃ (Δ : (Fin n → ZMod m) → (Fin n → ZMod m) → ZMod p) (R : ℕ)
      (Φ Ψ : (Fin n → ZMod m) → Fin R → ZMod p),
      (∀ x y, x ⬝ᵥ y = β → Δ x y = 1) ∧
      (∀ x y, x ⬝ᵥ y = 0 ∨ x ⬝ᵥ y = α → Δ x y = 0) ∧
      R ≤ n ^ d ∧
      (∀ x y, Δ x y = Φ x ⬝ᵥ Ψ y) ∧
      (∀ (h : ℕ), 1 ≤ h →
        R ^ h ≤ n ^ (d * h) ∧
        (∀ x y : Fin h → Fin n → ZMod m,
          ∏ ℓ, Δ (x ℓ) (y ℓ) =
            tensorVec (fun ℓ => Φ (x ℓ)) ⬝ᵥ tensorVec (fun ℓ => Ψ (y ℓ))) ∧
        (∀ (ι κ : Type) [Fintype ι] [Fintype κ]
          (x : Fin h → ι → Fin n → ZMod m) (y : Fin h → κ → Fin n → ZMod m),
          (Matrix.of fun i j => ∏ ℓ, Δ (x ℓ i) (y ℓ j)).rank ≤ n ^ (d * h))) := by sorry

end MatchVec3
