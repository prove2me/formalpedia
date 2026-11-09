-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_circuits_for_factors
-- name    : NCFactorClosure607.Circuits.circuits_for_factors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:31.874208+00:00
-- url     : https://prove2.me/theorems/1358ab48-9471-421c-bca5-05af3ed9c127
-- title:
--   Theorem 1.1: one-sided factors of a size-$s$ degree-$D$ noncommutative circuit have circuits of size $O(sD^3)$, central factors $O(sD^6)$
-- statement:
--   Let $F$ be a field and $X$ a set of noncommuting variables. Let a noncommutative circuit $C$ of size $s$ compute a nonzero polynomial $f\in F\langle X\rangle$ of degree at most $D$, where $D\ge1$. There is an absolute constant $K$ (independent of $F$, $X$, $C$, $s$, $D$ and the factors) such that:
--
--   1. If $f=gh$ with $g,h\neq0$, then each of $g$ and $h$ has a circuit of size at most
--   $$K\,s\,D^3 .$$
--   The circuit for $g$ is constructed from $C$ and cofactor data for $h$ (a maximum-degree word $v$ of $h$, its nonzero coefficient $c=[v]h$, and the coefficients in $h$ of all proper suffixes of $v$, including the empty suffix); the circuit for $h$ is constructed from $C$ and the analogous data for $\mathrm{rev}(g)$.
--   2. If $f=agb$ with $a,g,b\neq0$, then $g$ has a circuit of size at most
--   $$K\,s\,D^6,$$
--   constructed from $C$ and cofactor data for $b$ and for $\mathrm{rev}(a)$; the two words have length at most $D$. This covers central factors as well as one-sided factors.
--
--   For every choice of valid cofactor data, the constructed circuit computes the specified factor, has syntactic degree at most that of $C$, and its constants are constants of $C$ or among $0$, $1$, $c^{-1}$ and $-d_\ell c^{-1}$ for the supplied data. A scalar cofactor $c$ requires only its nonzero value.
--
--   The bound holds for every specified factorization (noncommutative factorizations need not be unique), over every field and for nonhomogeneous polynomials. It shows that noncommutative circuits of polynomial size and degree are closed under taking factors, and that a lower bound for $g$ transfers to every multiple $agb$ of polynomially bounded degree.
--
--   **Formalization Note** $\mathrm{rev}$ is Mathlib's `star` on `FreeAlgebra F X`. The constructions are the explicit functions `extractRight`, `extractLeft` and `extractCentral`; "valid cofactor data" is `ValidFor`, and such data exist for every nonzero cofactor (proved without `sorry` in the mission's verification file), so each clause yields the existence of the small circuit.
--
--   Differences from the source:
--   - generalization: $X=\{x_1,\dots,x_m\}$ with $m\ge1$ → an arbitrary type `X`; reason: the statement for every type specializes to every finite nonempty variable set.
--   - encoding: $O(sD^3)$ and $O(sD^6)$ → one natural constant $K$ quantified before the field, the variable type, the circuit, $D$ and the factors; reason: the standard reading of an absolute $O$-constant.
--   - reading: "the circuits can be constructed deterministically with poly$(s,D)$ field operations when the cofactor data are supplied" → the circuits are the values of explicit Lean functions of the input circuit and the data only, and their constants lie in the constants of $C$ together with $0$, $1$, $c^{-1}$, $-d_\ell c^{-1}$; reason: in the arithmetic model the only field arithmetic of the construction is computing these $O(D)$ constants, everything else is writing gates.
--   - encoding: "each of $g,h$ has a circuit of size $O(sD^3)$" → for every valid cofactor data the constructed circuit computes the factor within the bound; reason: valid data exist for every nonzero cofactor, so the existence of a small circuit follows.
--   - encoding: "two words of length at most $D$ and $O(D)$ field elements" → the two data words have length at most $D$; reason: validity fixes the number of field elements of each data set to one more than its word length.
--   - encoding: $\mathrm{rev}$ → Mathlib `star` on `FreeAlgebra`; reason: `star` reverses every word and fixes scalars, so it is the same map.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.2–3, Theorem 1.1 (Circuits for factors); proof p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Extraction

universe u v

namespace NCFactorClosure607.Circuits

/-- Theorem 1.1 (Circuits for factors), p.2–3. There is one absolute constant `K` such that
for every field `F`, every type `X` of noncommuting variables, every well-formed circuit `C` of
size `s` computing a nonzero `f ∈ F⟨X⟩` of degree at most `D ≥ 1`:

(i) if `f = g h` with `g, h ≠ 0`, then from any valid cofactor data for `h` the construction
`extractRight` outputs a circuit for `g`, and from any valid cofactor data for `rev g` the
construction `extractLeft` outputs a circuit for `h`; each has size at most `K s D³`;

(ii) if `f = a g b` with `a, g, b ≠ 0`, then from any valid cofactor data for `b` and for
`rev a` (two words of length at most `D`, `O(D)` field elements) the construction
`extractCentral` outputs a circuit for `g` of size at most `K s D⁶`.

Every output circuit is well-formed, has syntactic degree at most that of `C`, and uses as
constants only constants of `C` and the constants `0, 1, c⁻¹, -d_ℓ c⁻¹` of the supplied data. -/
theorem circuits_for_factors :
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (C : Circuit F X) (D : ℕ),
      C.WellFormed → 1 ≤ D → C.eval ≠ 0 → DegLE C.eval D →
      (∀ g h : FreeAlgebra F X, C.eval = g * h → g ≠ 0 → h ≠ 0 →
        (∀ data : CofactorData F X, data.ValidFor h →
          (extractRight C data).WellFormed ∧
          (extractRight C data).eval = g ∧
          (extractRight C data).size ≤ K * C.size * D ^ 3 ∧
          (extractRight C data).synDeg ≤ C.synDeg ∧
          (extractRight C data).consts ⊆ C.consts ∪ data.constSet) ∧
        (∀ data : CofactorData F X, data.ValidFor (star g) →
          (extractLeft C data).WellFormed ∧
          (extractLeft C data).eval = h ∧
          (extractLeft C data).size ≤ K * C.size * D ^ 3 ∧
          (extractLeft C data).synDeg ≤ C.synDeg ∧
          (extractLeft C data).consts ⊆ C.consts ∪ data.constSet)) ∧
      (∀ a g b : FreeAlgebra F X, C.eval = a * g * b → a ≠ 0 → g ≠ 0 → b ≠ 0 →
        ∀ dataB dataA : CofactorData F X, dataB.ValidFor b → dataA.ValidFor (star a) →
          dataB.b ≤ D ∧ dataA.b ≤ D ∧
          (extractCentral C dataB dataA).WellFormed ∧
          (extractCentral C dataB dataA).eval = g ∧
          (extractCentral C dataB dataA).size ≤ K * C.size * D ^ 6 ∧
          (extractCentral C dataB dataA).synDeg ≤ C.synDeg ∧
          (extractCentral C dataB dataA).consts ⊆
            C.consts ∪ dataB.constSet ∪ dataA.constSet) := by sorry

end NCFactorClosure607.Circuits
