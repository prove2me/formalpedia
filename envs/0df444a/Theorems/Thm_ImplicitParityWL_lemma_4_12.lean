-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_4_12
-- name    : ImplicitParityWL.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:10:47.042001+00:00
-- url     : https://prove2.me/theorems/1975e062-24c2-429a-a635-326903f4427d
-- title:
--   Lemma 4.12 — extending partial seeds
-- statement:
--   Fix $k\ge3$ and $\ell\ge1$. Let $S\subseteq T\subseteq\mathfrak c$ with $|T|\le k+1$, and let $z\in\mathbb F_2^S$ with $x\cdot z=0$ for all block-even $x\in C$ with $\mathrm{supp}(x)\subseteq S$. Then $z$ extends to a seed $z'\in\mathbb F_2^T$ with the same property on $T$. Additionally, if there is an address $a\in\Sigma$ with $\mathrm{supp}(a)\subseteq T$, its value $a\cdot z'$ may be prescribed arbitrarily, provided it agrees with $a\cdot z$ when $\mathrm{supp}(a)\subseteq S$.
--
--   Duplicator uses this to answer a newly announced coordinate color with a prescribed variable value.
--
--   **Formalization Note** The two sentences of the lemma are the two conjuncts of the conclusion.
--
--   Differences from the source:
--   - encoding: z ∈ 𝔽₂^S, z′ ∈ 𝔽₂^T → total functions on 𝔠, agreeing on S; reason: only the values on S and T are read
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 4.12, pp.21–22

import Mathlib
import Definitions.Def_ImplicitParityWL_Address

namespace ImplicitParityWL

/-- **Lemma 4.12** (Extending partial seeds; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, pp.21–22): let `S ⊆ T ⊆ 𝔠` with `|T| ≤ k + 1` and let `z` be a seed on
`S` with `x · z = 0` for all block-even `x ∈ C` with `supp(x) ⊆ S`. Then `z` extends to a seed `z'` on `T` with the
same property on `T`. Additionally, if there is an address `a` with `supp(a) ⊆ T`, its value `a · z'` may be prescribed
arbitrarily, provided it agrees with `a · z` when `supp(a) ⊆ S`.

**Formalization Note** A seed on `S` is a total function of which only the values on `S` are read. -/
theorem lemma_4_12 (k ℓ : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) (S T : Finset (Coord k ℓ)) (hST : S ⊆ T)
    (hT : T.card ≤ k + 1) (z : Word k ℓ)
    (hz : ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ S → x.dot z = 0) :
    (∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
      ∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → x.dot z' = 0) ∧
    (∀ (a : Address k ℓ) (β : ZMod 2), a.supp ⊆ T → (a.supp ⊆ S → a.dot z = β) →
      ∃ z' : Word k ℓ, (∀ c ∈ S, z' c = z c) ∧
        (∀ x : Word k ℓ, x.IsBlockEven → x.supp ⊆ T → x.dot z' = 0) ∧ a.dot z' = β) := by sorry

end ImplicitParityWL
