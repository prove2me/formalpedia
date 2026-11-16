-- Prove2me | Theorems.Thm_GoodQLTC_Supplement_theorem_11_1
-- name    : GoodQLTC.Supplement.theorem_11_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:01:08.685577+00:00
-- url     : https://prove2.me/theorems/7f366f49-9c95-419f-a748-e9f632939e92
-- title:
--   Theorem 11.1 — arithmetic realization: regular $\lambda$-expanding cubical quotients of products of Bruhat–Tits trees
-- statement:
--   Fix integers $t\ge1$, $r\ge3$ and $0\le a_1<\dots<a_t$. Put $q_i:=2^{r+a_i}$, $n_i:=q_i+1$ and
--   $$\lambda:=\max_{i\in[t]}\frac{2\sqrt{q_i}}{q_i+1}<1.$$
--   There are a totally real number field $K$, a totally definite quaternion algebra $B/K$, a maximal order $\mathcal M$, and distinct finite places $v_1,\dots,v_t$ of $K$ at which $B$ splits, with residue fields of size $|k_{v_i}|=q_i$, together with splittings $\varphi_i:B_{v_i}\cong M_2(K_{v_i})$ such that $\varphi_i(\mathcal M_{v_i})=M_2(\mathcal O_{v_i})$ and $\varphi_i$ carries the norm-one group $H(K_{v_i})$ onto $\mathrm{SL}_2(K_{v_i})$. There is a nested family of norm-one congruence groups $\{\Gamma_\nu\}_\nu$ (levels $\mathfrak n_0\supseteq\mathfrak n_1\supseteq\cdots$, nonzero and prime to every $v_i$) acting on $\mathcal T:=\prod_iT(K_{v_i})$ through the $\varphi_i$, such that:
--
--   1. each action is free on the faces of $\mathcal T$ and preserves all parities, and $X_\nu:=\Gamma_\nu\backslash\mathcal T$ is a regular, $\lambda$-expanding cubical complex with degrees $\{n_i\}_{i\in[t]}$;
--   2. for every $f\in\mathcal T$, the quotient map induces a poset isomorphism $\mathcal T_{\ge f}\to(X_\nu)_{\ge[f]}$;
--   3. $V_\nu:=2^{-t}|X_\nu(0)|\to\infty$.
--
--   This is the source of the cubical complexes on which the paper's codes live: Theorems 4.13 and 14.1 build the compatible Reed–Solomon cosheaves on these quotients.
--
--   **Formalization Note** The arithmetic objects (quaternion algebra, totally definite, reduced norm, maximal order, $\mathcal M_v$, the groups $\Gamma_\nu$) are those of `GoodQLTC.Supplement.normOneCongruenceGroup`; the trees, parities, labels, orbit poset and upward-star isomorphisms are those of `GoodQLTC.Supplement.ProductFace`; cubical complex, regularity, $\lambda$-expansion and $X(0)$ are the published `GoodQLTC.IsCubicalComplex`, `GoodQLTC.IsRegular`, `GoodQLTC.IsExpanding` and `GoodQLTC.numFaces`. The orbit poset is a finite poset $X_\nu$ with a surjection from the faces of $\mathcal T$ with the orbit, order and label properties.
--
--   Differences from the source:
--   - reading: a nested family of norm-one congruence groups (term not defined in the statement) → Γ_ν = {x ∈ B : nrd x = 1, x_v ∈ M_v for finite v ∉ S, x_v − 1 ∈ 𝔫_ν M_v for finite v ∣ 𝔫_ν} for nonzero ideals 𝔫_0 ⊇ 𝔫_1 ⊇ ⋯ of O_K prime to every v_i; reason: the paper's groups (11.1) are this family for 𝔫_ν = 3^{ν+ν₀}O_K (3 inert, after the reindexing of p.38), so the existential statement under this reading is what is proved; the groups are pinned, not arbitrary
--   - encoding: orbit poset X_ν := Γ_ν\T with [f] ≤ [g] iff γf ≤ g → a finite poset X_ν with a surjection p_ν from the faces such that p_ν f = p_ν g iff γf = g, p_ν f ≤ p_ν g iff γf ≤ g (γ ∈ Γ_ν), labels inherited; reason: this characterizes the orbit poset up to isomorphism; finiteness and the poset axioms are asserted, not assumed
--   - encoding: nrd(x) = x x̄ = 1 → det ψ(1 ⊗ x) = 1 for every extension E/F and every splitting ψ : E ⊗ B ≅ M₂(E); reason: for a quaternion algebra det ψ(1 ⊗ x) = nrd(x) for every splitting, and splittings exist
--   - encoding: the local projective norm-one actions are SL₂(K_{v_i})/{±I₂}, with the endpoint stabilizers and reductions of Lemma 11.3 → φ_i maps the norm-one elements of B_{v_i} onto SL₂(K_{v_i}), and Γ_ν acts through x ↦ φ_i(1 ⊗ x); reason: Lemma 11.3 is an unconditional lemma about SL₂(L)/{±I₂} acting on T(L) and adds no condition on the objects
--   - encoding: lattices free of rank two spanning L², adjacency πΛ ⊊ Λ' ⊊ Λ; parity v_L(det g) mod 2 → the published Bruhat–Tits tree (finitely generated lattices spanning L², adjacency with an irreducible ϖ); parity odd iff det g ∉ O^×(L^×)²; reason: over a discrete valuation ring these are the same lattices, the same adjacency and the same parity
--   - encoding: the family {Γ_ν}_{ν≥1}; |k_{v_i}| = q_i → indexed by ν ∈ ℕ; |O_K/v_i| = q_i; reason: an index shift; the residue field of v_i is O_K/v_i
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 11.1, pp.33–34 (PDF 36–37); groups (11.1), p.36 (PDF 39)

import Mathlib
import Definitions.Def_GoodQLTC_dir
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_IsExpanding
import Definitions.Def_GoodQLTC_Supplement_ProductFace
import Definitions.Def_GoodQLTC_Supplement_normOneCongruenceGroup

namespace GoodQLTC.Supplement

open GoodQLTC NumberField TensorProduct IsDedekindDomain Filter

/-- **Theorem 11.1** (arithmetic realization of the cubical complexes), Gay–Jeronimo,
arXiv:2609.20780 (held version), pp.33–34. Fix integers `t ≥ 1`, `r ≥ 3` and `0 ≤ a_1 < ⋯ < a_t`;
put `q_i := 2^{r+a_i}`, `n_i := q_i + 1` and `λ := max_i 2√q_i/(q_i + 1)`. There are a totally real
number field `K`, a totally definite quaternion algebra `B/K`, a maximal order `M`, distinct finite
places `v_i` with `|k_{v_i}| = q_i` at which `B` splits, with splittings `φ_i : B_{v_i} ≅ M₂(K_{v_i})`
taking `M_{v_i}` onto `M₂(O_{v_i})` (and the norm-one group `H(K_{v_i})` onto `SL₂(K_{v_i})`), and a
nested family of norm-one congruence groups `Γ_ν` acting on `T := ∏_i T(K_{v_i})` through the
`φ_i`, such that
1. each action is free on the faces of `T` and preserves all parities, and `X_ν := Γ_ν\T` is a
   regular, `λ`-expanding cubical complex with degrees `{n_i}`;
2. for every `f ∈ T` the quotient map induces a poset isomorphism `T_{≥f} → (X_ν)_{≥[f]}`;
3. `V_ν := 2^{−t}|X_ν(0)| → ∞`.

**Formalization Note.** Quaternion algebra, totally definite, reduced norm, (maximal) order, `M_v`,
and the congruence groups are the definitions of this module set (`IsQuaternionAlgebra`,
`IsTotallyDefinite`, `IsReducedNormOne`, `IsMaximalOrder`, `localSpan`, `normOneCongruenceGroup`).
"Norm-one congruence groups" is read as: `Γ_ν = {x ∈ B : nrd x = 1, x_v ∈ M_v for finite v ∉ S,
x_v − 1 ∈ 𝔫_ν M_v for finite v ∣ 𝔫_ν}` for nonzero ideals `𝔫_0 ⊇ 𝔫_1 ⊇ ⋯` of `O_K` prime to every
`v_i` (the paper's groups (11.1) are `𝔫_ν = 3^{ν+ν₀} O_K`). `x ∈ Γ_ν` acts on the `i`-th tree by
`φ_i(1 ⊗ x) ∈ SL₂(K_{v_i})` (`splitAct`) and on `T` coordinatewise. `T(K_v)` is the published
Bruhat–Tits tree over `O_v := v.adicCompletionIntegers K`. The orbit poset `X_ν` is packaged as a
finite poset `X ν` with a surjection `p ν` satisfying `IsOrbitQuotient` (orbits, orbit order
`[f] ≤ [g] ⟺ ∃ γ, γ f ≤ g`, inherited labels), so finiteness and the poset axioms are asserted, not
assumed. The family is indexed by `ν ∈ ℕ` (the paper's `ν ≥ 1`); `|k_v|` is `|O_K/v|`. The last
sentence's "local projective norm-one actions are `SL₂(K_{v_i})/{±I₂}`" is the clause
`φ_i(H(K_{v_i})) = SL₂(K_{v_i})` together with the action through `φ_i`; Lemma 11.3 is an
unconditional lemma about that group and adds nothing to the statement. -/
theorem theorem_11_1 (t r : ℕ) (a : Fin t → ℕ) (ht : 1 ≤ t) (hr : 3 ≤ r) (ha : StrictMono a) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (B : Type) (_ : Ring B) (_ : Algebra K B)
      (M : Subring B) (v : Fin t → HeightOneSpectrum (𝓞 K))
      (φ : ∀ i, (v i).adicCompletion K ⊗[K] B ≃ₐ[(v i).adicCompletion K]
        Matrix (Fin 2) (Fin 2) ((v i).adicCompletion K))
      (𝔫 : ℕ → Ideal (𝓞 K)),
      IsTotallyReal K ∧ IsQuaternionAlgebra K B ∧ IsTotallyDefinite K B ∧ IsMaximalOrder K M ∧
      Function.Injective v ∧
      (∀ i, Nat.card (𝓞 K ⧸ (v i).asIdeal) = 2 ^ (r + a i)) ∧
      (∀ i, φ i '' localSpan (v i) (M : Set B) =
        {A | ∀ j k, A j k ∈ (v i).adicCompletionIntegers K}) ∧
      (∀ i, φ i '' {y | IsReducedNormOne (F := (v i).adicCompletion K) y} = {A | A.det = 1}) ∧
      (∀ ν, 𝔫 ν ≠ ⊥ ∧ 𝔫 (ν + 1) ≤ 𝔫 ν ∧ ∀ i, ¬ 𝔫 ν ≤ (v i).asIdeal) ∧
      (∀ ν, normOneCongruenceGroup M v (𝔫 (ν + 1)) ⊆ normOneCongruenceGroup M v (𝔫 ν)) ∧
      (∀ ν, ∀ γ ∈ normOneCongruenceGroup M v (𝔫 ν),
        (∀ f : ProductFace (fun i => (v i).adicCompletionIntegers K),
          faceAct (splitAct φ γ) f.1 = f.1 → γ = 1) ∧
        ∀ i x, vertexParity ((v i).adicCompletionIntegers K) (splitAct φ γ i • x) =
          vertexParity ((v i).adicCompletionIntegers K) x) ∧
      ∃ (X : ℕ → Type) (_ : ∀ ν, PartialOrder (X ν)) (_ : ∀ ν, Fintype (X ν))
        (p : ∀ ν, ProductFace (fun i => (v i).adicCompletionIntegers K) → X ν)
        (φX : ∀ ν, X ν → Fin t → Option Bool),
        (∀ ν, IsOrbitQuotient (splitAct φ) (normOneCongruenceGroup M v (𝔫 ν)) (p ν) (φX ν) ∧
          IsCubicalComplex t (φX ν) ∧
          IsRegular (φX ν) (fun i => 2 ^ (r + a i) + 1) ∧
          IsExpanding (φX ν) (fun i => 2 ^ (r + a i) + 1)
            (⨆ i : Fin t, 2 * Real.sqrt ((2 : ℝ) ^ (r + a i)) / ((2 : ℝ) ^ (r + a i) + 1)) ∧
          IsUpwardStarIso (p ν)) ∧
        Tendsto (fun ν => (numFaces (φX ν) 0 : ℝ) / 2 ^ t) atTop atTop := by sorry

end GoodQLTC.Supplement
