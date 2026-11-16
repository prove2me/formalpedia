-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_7_8
-- name    : GL2QFT.Supplement.theorem_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:50.063018+00:00
-- url     : https://prove2.me/theorems/12bbde52-6358-4ddb-9408-bbf5210c8b16
-- title:
--   Theorem 7.8 — $\widehat G$ is in bijection with $L_N=\{(\sigma,\eta):\sigma\in O(\widehat N),\ \eta\in N^+_{N\le I_\sigma}(\sigma)\}$
-- statement:
--   Let $N\trianglelefteq G$ be finite groups. Fix representatives $R_\lambda$ of $\widehat N$, a set $O(\widehat N)$ of representatives of the $G$-orbits on $\widehat N$, and for every $\sigma\in O(\widehat N)$ representatives $R_\eta$ of the irreps of the inertia group $I_\sigma$ and a left transversal $T_\sigma$ of $I_\sigma$ containing $1$. Then the map
--   $$\Phi:L_N\to\widehat G,\qquad \Phi(\sigma,\eta)=\mathrm{Ind}^G_{I_\sigma}(V_\eta),\qquad L_N=\{(\sigma,\eta):\sigma\in O(\widehat N),\ \eta\in N^+_{N\le I_\sigma}(\sigma)\} \tag{184}$$
--   is a bijection onto $\widehat G$:
--   1. every $\Phi(\sigma,\eta)$, $(\sigma,\eta)\in L_N$, is an irreducible unitary representation of $G$;
--   2. $\Phi(\sigma,\eta)\cong\Phi(\sigma',\eta')$ for pairs in $L_N$ implies $(\sigma,\eta)=(\sigma',\eta')$;
--   3. every irreducible representation of $G$ is equivalent to $\Phi(\sigma,\eta)$ for some $(\sigma,\eta)\in L_N$.
--
--   This is the Clifford classification of the irreps of $G$ through those of a normal subgroup; the little group method (Theorem 7.12) refines the successor sets.
--
--   Differences from the source:
--   - encoding: "$\widehat G$ is in bijection with $L_N$" → the map $\Phi$ of the proof lands in irreps, is injective on equivalence classes and hits every class; reason: $\widehat G$ is the set of equivalence classes; this is the bijection the proof and the text after it use
--   - generalization: the transversal $T_\sigma=\{g_{\sigma,\mu}\}$ of Definition 7.2 used in $\mathrm{Ind}$ → any left transversal of $I_\sigma$ containing $1$; reason: by Lemma 7.3 the paper's $T_\sigma$ is one of them
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 7.8, eq. (184), p.58 (PDF p.59); Definitions 7.1–7.2 p.56

import Definitions.Def_GL2QFT_Supplement_RepTheory

open Classical

namespace GL2QFT

namespace Supplement

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 7.8**, p.58 (PDF p.59): "Let
`N ⊴ G`. Then `Ĝ` is in bijection with the set `L_N := {(σ, η) : σ ∈ O(N̂) and η ∈ N⁺_{N≤I_σ}(σ)}`
(184)." The bijection is the map of the proof, `Φ(σ, η) := Ind^G_{I_σ}(V_η)`.

Data: a finite group `G`, a normal subgroup `N`, chosen representatives `R_λ` of `N̂`, a set `O` of
orbit representatives (Definition 7.2), for each `σ ∈ O` chosen representatives `R_η` of `Î_σ` and a
left transversal `T_σ` of `I_σ` containing `1` (Definition 2.10, Lemma 7.3). Conclusions:
1. for every `(σ, η) ∈ L_N`, `Φ(σ, η)` is an irreducible unitary representation of `G`;
2. `Φ(σ, η) ≅ Φ(σ', η')` with both pairs in `L_N` forces `(σ, η) = (σ', η')`;
3. every irreducible representation of `G` is equivalent to `Φ(σ, η)` for some `(σ, η) ∈ L_N`.

**Formalization Note** `Ĝ` (equivalence classes of irreps) is represented through the three
clauses: `Φ` lands in irreps, is injective on classes, and hits every class. The inertia group,
the orbit relation and the successor sets are `GL2QFT.Supplement.inertia`, `InOrbit` and
`IsSuccessor`; `Ind` is (27) (`indRep`). -/
theorem theorem_7_8 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (T : ΛN → Set G)
    (hT : ∀ σ ∈ O, Subgroup.IsComplement (T σ) (inertia N RN σ : Set G) ∧ (1 : G) ∈ T σ)
    (Λη : ΛN → Type) [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, inertia N RN σ → Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ)) :
    let L : Set (Σ σ : ΛN, Λη σ) := {p | p.1 ∈ O ∧ IsSuccessor N RN p.1 (Rη p.1 p.2)}
    let Φ : ∀ p : Σ σ : ΛN, Λη σ, G → Matrix (T p.1 × Bη p.1 p.2) (T p.1 × Bη p.1 p.2) ℂ :=
      fun p => indRep (inertia N RN p.1) (T p.1) (Rη p.1 p.2)
    (∀ p ∈ L, IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p ∈ L, ∀ p' ∈ L, RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ p ∈ L, RepEquiv (Φ p) ρ) := by sorry

end Supplement

end GL2QFT
