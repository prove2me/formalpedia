-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_8_7
-- name    : GL2QFT.Supplement.theorem_8_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T01:47:09.343192+00:00
-- url     : https://prove2.me/theorems/d0252d28-382d-4225-afc9-24ec56a8f605
-- title:
--   Theorem 8.7 — irreps of $F\wr S_n$ are labelled by unique pairs $(\sigma,\nu)$, $R_{(\sigma,\nu)}\cong\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_\nu)$
-- statement:
--   Let $F$ be a finite group with representatives $R_\rho$ of $\widehat F$ and a fixed total order on $\widehat F$, let $n\ge1$ and $G=F\wr S_n$. For every $m$ fix representatives $R_\nu$, $\nu\vdash m$, of the irreps of $S_m$. Every irreducible representation of $F\wr S_n$ can be labelled by a unique pair $(\sigma,\nu)$, where
--   $$\sigma=(\sigma_1^{n_1},\dots,\sigma_\ell^{n_\ell})\in O(\widehat N),\qquad \nu=(\nu_1,\dots,\nu_\ell),\quad \nu_r\vdash n_r, \tag{253}$$
--   ($\sigma$ nonincreasingly sorted, (234)–(235)), and a representative for the irreducible representation labelled by $(\sigma,\nu)$ is
--   $$R_{(\sigma,\nu)}\cong\mathrm{Ind}^G_{I_\sigma}\big(R^{\rm ext}_\sigma\otimes\tilde R_\nu\big) \tag{254}$$
--   with $I_\sigma=N\rtimes H_\sigma$, $R^{\rm ext}_\sigma$ from (248) and $\tilde R_\nu$ the inflation of $\bigotimes_rR_{\nu_r}$ on $H_\sigma=S_{n_1}\times\dots\times S_{n_\ell}$. That is: every $\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_\nu)$ is an irreducible unitary representation, two of them are equivalent only for equal labels, and every irreducible representation of $G$ is equivalent to one of them.
--
--   This classification gives the target basis (255) of the wreath-product QFT.
--
--   Differences from the source:
--   - generalization: $R_\nu$ the simple $S_m$-module labelled by $\nu$ → any complete family of pairwise inequivalent irreducible unitary representations of $S_m$ indexed by the partitions of $m$; reason: the classification holds for every such indexing, and the paper's is one of them
--   - generalization: the transversal $T_\sigma$ of (238) → any left transversal of $I_\sigma$ containing $1$; reason: (238) is one of them (Lemma 7.3)
--   - encoding: $\nu=(\nu_1,\dots,\nu_\ell)$ → a tuple $(\nu_\rho)_{\rho\in\widehat F}$ with $\nu_\rho\vdash n_\rho$ (the empty partition when $\rho$ does not occur in $\sigma$); reason: in bijection with the tuples of (249)
--   - encoding: $H_\sigma=S_{n_1}\times\dots\times S_{n_\ell}$ → the restriction of $\pi\in H_\sigma$ to each block, transported to $S_{n_\rho}$ along the increasing bijection; reason: Observation 8.5
--   - encoding: the bijection of labels and irreps → irreducibility, injectivity on equivalence classes and surjectivity onto them; reason: $\widehat G$ is the set of classes
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 8.7, eqs. (253)–(254), p.69 (PDF p.70); §8.1–8.2 eqs. (222)–(251) pp.66–69

import Definitions.Def_GL2QFT_Supplement_Wreath

open Classical

namespace GL2QFT

namespace Supplement

open Wreath

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 8.7 (Irreducible representations
of `F ≀ S_n`)**, p.69 (PDF p.70): "Every irreducible representation of `F ≀ S_n` can be labeled by a
unique pair `(σ, ν)`, where `σ = (σ_1^{n_1}, …, σ_ℓ^{n_ℓ}) ∈ O(N̂)`, `ν = (ν_1, …, ν_ℓ)`, `ν_r ⊢ n_r`
(253). A representative for the irreducible representation labeled by `(σ, ν)` is
`R_(σ,ν) ≅ Ind^G_{I_σ}(R^ext_σ ⊗ R̃_ν)` (254)."

Data: a finite group `F` with representatives `R_ρ` of `F̂` and a fixed total order on `F̂`;
`n ≥ 1`; for every `m` representatives `R_ν` of `Ŝ_m` indexed by the partitions `ν ⊢ m`; for every
nonincreasingly sorted `σ ∈ F̂^n` ((234)–(235): the orbit representatives `O(N̂)`) a left transversal
`T_σ` of `I_σ = N ⋊ H_σ` containing `1`. With
`Φ(σ, ν) := Ind^G_{I_σ}(R^ext_σ ⊗ R̃_ν)` ((248), (251), Definition 2.10):
1. every `Φ(σ, ν)` is an irreducible unitary representation of `G = F ≀ S_n`;
2. `Φ(σ, ν) ≅ Φ(σ', ν')` forces `(σ, ν) = (σ', ν')` (uniqueness of the label);
3. every irreducible representation of `G` is equivalent to some `Φ(σ, ν)` (existence).

**Formalization Note** `ν` is a tuple `(ν_ρ)_{ρ ∈ F̂}` with `ν_ρ ⊢ n_ρ`, the number of positions of
`ρ` in `σ` (see `littleRep`). The statement holds for every indexing of `Ŝ_m` by partitions and for
every transversal `T_σ`. -/
theorem theorem_8_7 (F : Type) [Group F] [Fintype F] (n : ℕ) (hn : 1 ≤ n)
    {ΛF : Type} [Fintype ΛF] [LinearOrder ΛF] (BF : ΛF → Type) [∀ ρ, Fintype (BF ρ)]
    [∀ ρ, DecidableEq (BF ρ)] (RF : ∀ ρ, F → Matrix (BF ρ) (BF ρ) ℂ) (hRF : IsIrrepSystem RF)
    (BS : ∀ m, Nat.Partition m → Type) [∀ m ν, Fintype (BS m ν)] [∀ m ν, DecidableEq (BS m ν)]
    (RS : ∀ m (ν : Nat.Partition m), Equiv.Perm (Fin m) → Matrix (BS m ν) (BS m ν) ℂ)
    (hRS : ∀ m, IsIrrepSystem (RS m))
    (T : (Fin n → ΛF) → Set (WP F n))
    (hT : ∀ σ : Fin n → ΛF, Antitone σ →
      Subgroup.IsComplement (T σ) (inertiaW (F := F) σ : Set (WP F n)) ∧ (1 : WP F n) ∈ T σ) :
    let Lab : Type :=
      Σ σ : {σ : Fin n → ΛF // Antitone σ}, ∀ ρ, Nat.Partition (Fintype.card (block σ.1 ρ))
    let Φ : ∀ p : Lab, WP F n →
        Matrix (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ))))
          (T p.1.1 × ((∀ r, BF (p.1.1 r)) × (∀ ρ, BS _ (p.2 ρ)))) ℂ :=
      fun p => indRep (inertiaW (F := F) p.1.1) (T p.1.1)
        (fun x => Matrix.kronecker (extRep RF p.1.1 x) (littleRep RS p.1.1 p.2 x))
    (∀ p : Lab, IsUnitaryRep (Φ p) ∧ IsIrreducibleRep (Φ p)) ∧
    (∀ p p' : Lab, RepEquiv (Φ p) (Φ p') → p = p') ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : WP F n → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ p : Lab, RepEquiv (Φ p) ρ) := by sorry

end Supplement

end GL2QFT
