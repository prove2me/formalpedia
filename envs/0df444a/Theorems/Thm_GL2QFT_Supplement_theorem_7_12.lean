-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_7_12
-- name    : GL2QFT.Supplement.theorem_7_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T01:45:29.374722+00:00
-- url     : https://prove2.me/theorems/a1fc1f6c-dee8-41bc-b1c3-89399085b628
-- title:
--   Theorem 7.12 (Little group method) — $\widehat G\leftrightarrow\{(\sigma,\eta')\}$, $R_{(\sigma,\eta')}\cong\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_{\eta'})$
-- statement:
--   Let $N\trianglelefteq G$ be finite groups and fix representatives $R_\lambda$ of $\widehat N$. Suppose that every $R_\lambda$ extends to a fixed unitary representation $R^{\rm ext}_\lambda$ of its inertia group $I_\lambda$ (194). Fix a set $O(\widehat N)$ of orbit representatives and, for $\sigma\in O(\widehat N)$, representatives $R_{\eta'}$ of the irreps of the little group $H_\sigma=I_\sigma/N$ and a left transversal $T_\sigma$ of $I_\sigma$ containing $1$. Then there is a bijection
--   $$\widehat G\longleftrightarrow\{(\sigma,\eta'):\sigma\in O(\widehat N),\ \eta'\in\widehat H_\sigma\}, \tag{195}$$
--   under which the irrep labelled by $(\sigma,\eta')$ is
--   $$R_{(\sigma,\eta')}\cong\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_{\eta'}),\qquad V_{(\sigma,\eta')}\cong\mathrm{Ind}^G_{I_\sigma}(V_\sigma\otimes V_{\eta'}), \tag{196}$$
--   with $\tilde R_{\eta'}$ the inflation of $R_{\eta'}$ to $I_\sigma$. That is: every such induced representation is irreducible and unitary, two of them are equivalent only for equal labels, and every irrep of $G$ is equivalent to one of them.
--
--   The little group method describes $\widehat G$ through $\widehat N$ and the irreps of the little groups; it underlies Algorithm 2 and the classification for $F\wr S_n$ (Theorem 8.7).
--
--   Differences from the source:
--   - encoding: the bijection (195) with the construction (196) → the map $(\sigma,\eta')\mapsto\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_{\eta'})$ lands in irreps, is injective on equivalence classes and hits every class; reason: $\widehat G$ is the set of equivalence classes; the bijection is the one given by (196)
--   - generalization: the transversal $T_\sigma$ of Definition 7.2 → any left transversal of $I_\sigma$ containing $1$; reason: by Lemma 7.3 the paper's $T_\sigma$ is one of them
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 7.12, eqs. (194)–(196), p.60 (PDF p.61); Definitions 7.9–7.10 p.59

import Definitions.Def_GL2QFT_Supplement_RepTheory

open Classical

namespace GL2QFT

namespace Supplement

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 7.12 (Little group method)**, p.60
(PDF p.61): "Let `N ⊴ G`. Suppose that, for all `λ ∈ N̂`, `R_λ : N → U(V_λ)` extends to a fixed
`R^ext_λ : I_λ → U(V_λ)` (194). Then there is a bijection `Ĝ ↔ {(σ, η′) : σ ∈ O(N̂), η′ ∈ Ĥ_σ}`
(195). Namely the `G`-irreducible representation labeled by `(σ, η′)`, which we denote by
`(R_(σ,η′), V_(σ,η′))`, can be constructed as `R_(σ,η′) ≅ Ind^G_{I_σ}(R^ext_σ ⊗ R̃_{η′})`,
`V_(σ,η′) ≅ Ind^G_{I_σ}(V_σ ⊗ V_{η′})` (196)."

Data: a finite group `G`, `N ⊴ G`, representatives `R_λ` of `N̂`, fixed extensions `R^ext_λ` of every
`R_λ` to `I_λ` (194), a set `O` of orbit representatives, for each `σ ∈ O` representatives `R_{η′}`
of the dual of the little group `H_σ = I_σ / N` and a left transversal `T_σ` of `I_σ` containing
`1`. With `Φ(σ, η′) := Ind^G_{I_σ}(R^ext_σ ⊗ R̃_{η′})` (`R̃` the inflation, Definition 7.10):
1. every `Φ(σ, η′)`, `σ ∈ O`, is an irreducible unitary representation of `G`;
2. `Φ(σ, η′) ≅ Φ(σ'', η'')` (both `σ, σ'' ∈ O`) forces `(σ, η′) = (σ'', η'')`;
3. every irreducible representation of `G` is equivalent to some `Φ(σ, η′)` with `σ ∈ O`.

**Formalization Note** The bijection (195) is the map `(σ, η′) ↦ [Φ(σ, η′)]` given by (196); the
carrier `ℂ[T_σ] ⊗ (V_σ ⊗ V_{η′})` of `Φ(σ, η′)` is the space `Ind^G_{I_σ}(V_σ ⊗ V_{η′})` of (196).
`H_σ` is the quotient group `I_σ ⧸ (N ∩ I_σ)` (`N ≤ I_σ`, p.59). -/
theorem theorem_7_12 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    (Λη : ΛN → Type) [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ)) :
    let Φ : ∀ p : Σ σ : ΛN, Λη σ,
        G → Matrix (T p.1 × (BN p.1 × Bη p.1 p.2)) (T p.1 × (BN p.1 × Bη p.1 p.2)) ℂ :=
      fun p => indRep (inertia N RN p.1) (T p.1)
        (fun k => Matrix.kronecker (Rext p.1 k) (inflation N RN p.1 (Rη p.1 p.2) k))
    (∀ p : Σ σ : ΛN, Λη σ, p.1 ∈ O → IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p p' : Σ σ : ΛN, Λη σ, p.1 ∈ O → p'.1 ∈ O → RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ →
        ∃ p : Σ σ : ΛN, Λη σ, p.1 ∈ O ∧ RepEquiv (Φ p) ρ) := by sorry

end Supplement

end GL2QFT
