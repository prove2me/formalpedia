-- Prove2me | Theorems.Thm_HypRecov_proposition_2_1
-- name    : HypRecov.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:40.56489+00:00
-- url     : https://prove2.me/theorems/4f6801f6-d713-44ba-a775-9c5f076f6320
-- title:
--   Proposition 2.1 — linear measurement interface
-- statement:
--   Let $1\le q\le r\le n$ and let $\mathbb F$ be a field of characteristic zero or characteristic greater than $r$. Let $W_{q,r}$ be the inclusion matrix of $q$-sets in $r$-sets of $V=\{0,\dots,n-1\}$ and $y=W_{q,r}x$ the projection of an edge-indicator vector $x\in\{0,1\}^{\binom{V}{r}}$.
--
--   1. For a function $P$ on $\binom{V}{r}$, there is a linear functional $L$ with $L(W_{q,r}x)=\sum_e x_eP(e)$ for every $x\in\{0,1\}^{\binom Vr}$ if and only if $P$ lies in the row span of $W_{q,r}$.
--   2. The row span of $W_{q,r}$ is the set of functions $e\mapsto\sum_{B\subseteq e,\,|B|\le q}c_B$, i.e. the restrictions to $r$-sets of multilinear polynomials $\sum_{|B|\le q}c_BX_B$ of degree at most $q$, where $X_B(e)=\mathbf 1[B\subseteq e]$.
--   3. For such $P$, the fragment update $g_P(A)=\sum_{B\subseteq A}c_B\big/\binom{r-|B|}{q-|B|}$ satisfies, for every $r$-set $e$,
--   $$\sum_{A\subseteq e,\ |A|=q}g_P(A)=P(e).$$
--
--   The proposition identifies the measurements a projection-stream sketch can maintain: exactly the degree-$q$ features of an edge, assembled from its fragments.
--
--   Differences from the source:
--   - encoding: characteristic zero or characteristic greater than r → (r! : 𝕜) ≠ 0; reason: equivalent for a field
--   - encoding: (V choose r), x ∈ {0,1}^(n choose r), the row span of W_{q,r} → subtypes {e // e.card = r}, x : r-sets → Bool, Submodule.span of the rows; reason: Lean convention; same objects
--   - encoding: restrictions of multilinear polynomials of degree at most q → functions e ↦ Σ_{B ⊆ e, |B| ≤ q} c_B; reason: X_B(e) = 1[B ⊆ e], so the two sets are equal
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Proposition 2.1, p.5 (PDF p.6), eq. (3)

import Mathlib
import Definitions.Def_HypRecov_inclusionMatrix

namespace HypRecov

/-- **Proposition 2.1 (Linear measurement interface).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Proposition 2.1,
p.5 (PDF p.6): "Let 1 ≤ q ≤ r ≤ n. Over a field of characteristic zero or characteristic greater
than r, a latent-edge measurement Σ_e x_e P(e) can be obtained by a linear map of y if and only if the
function P on (V choose r) lies in the row span of W_{q,r}. This row span is exactly the restrictions
of multilinear polynomials of degree at most q. For P = Σ_{|B|≤q} c_B X_B, one possible fragment
update is g_P(A) = Σ_{B⊆A} c_B / (r−|B| choose q−|B|). (3)"

Three clauses: (a) a linear functional `L` of `y = W_{q,r} x` returns `Σ_e x_e P(e)` for every
`x ∈ {0,1}^{(n choose r)}` iff `P` is in the row span; (b) the row span is the set of functions
`e ↦ Σ_{B ⊆ e, |B| ≤ q} c_B`; (c) the update identity `Σ_{A ⊆ e, |A| = q} g_P(A) = P(e)`.

**Formalization Note.** "Characteristic zero or characteristic greater than r" is `(r! : 𝕜) ≠ 0`,
which is equivalent. `X_B(e) = 1[B ⊆ e]`, so a multilinear polynomial restricted to `r`-sets is
`e ↦ Σ_{B ⊆ e} c_B`. -/
theorem proposition_2_1 (𝕜 : Type) [Field 𝕜] (n q r : ℕ) (hq : 1 ≤ q) (hqr : q ≤ r)
    (hrn : r ≤ n) (hchar : (r.factorial : 𝕜) ≠ 0) :
    (∀ P : {e : Finset (Fin n) // e.card = r} → 𝕜,
      (∃ L : ({A : Finset (Fin n) // A.card = q} → 𝕜) →ₗ[𝕜] 𝕜,
          ∀ x : {e : Finset (Fin n) // e.card = r} → Bool,
            L ((inclusionMatrix 𝕜 n q r).mulVec (fun e => if x e then 1 else 0)) =
              ∑ e, (if x e then (1 : 𝕜) else 0) * P e) ↔
        P ∈ Submodule.span 𝕜 (Set.range (inclusionMatrix 𝕜 n q r))) ∧
    ((Submodule.span 𝕜 (Set.range (inclusionMatrix 𝕜 n q r)) :
        Set ({e : Finset (Fin n) // e.card = r} → 𝕜)) =
      {P | ∃ c : Finset (Fin n) → 𝕜, ∀ e,
        P e = ∑ B ∈ e.1.powerset.filter (fun B => B.card ≤ q), c B}) ∧
    ∀ (c : Finset (Fin n) → 𝕜) (e : {e : Finset (Fin n) // e.card = r}),
      ∑ A ∈ e.1.powersetCard q,
          ∑ B ∈ A.powerset, c B / (((r - B.card).choose (q - B.card) : ℕ) : 𝕜) =
        ∑ B ∈ e.1.powerset.filter (fun B => B.card ≤ q), c B := by sorry

end HypRecov
