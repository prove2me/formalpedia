-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_C_2
-- name    : GL2QFT.Supplement.theorem_C_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T01:47:41.770647+00:00
-- url     : https://prove2.me/theorems/09bedf76-247a-4871-99ac-0127f0057560
-- title:
--   Theorem C.2 (Mackey induction with multiplicities) — $A_\lambda N_\lambda=U^\lambda_{\rm Ind}$, every $A_{\lambda,\nu}$ unitary
-- statement:
--   Let $G$ be a finite group, $H\le G$ and $\lambda\in\widehat H$. Keep $\Omega$, $H_\omega$, $T_\omega$ and $T=\bigsqcup T_\omega\omega$ of Remark 5.2, but drop multiplicity-freeness and $H_\omega$-adaptedness: fix representatives of the irreps of $H$, $G$ and every $H_\omega$, the bases of the $G$-irreps subgroup-adapted to $H$ with multiplicities (Definition B.1), and any choice of the embeddings $L^\omega_{\kappa,\nu,m}$ and $E^\omega_{\lambda,\kappa,e}$ of (290). Then
--   1. the circuit of Figure 20 implements $U^\lambda_{\rm Ind}$ of (291) in the bases of §C.1:
--   $$A_\lambda N_\lambda=U^\lambda_{\rm Ind},$$
--   with $N_\lambda$ its first three steps and $A_\lambda=\bigoplus_\nu I_{V_\nu}\otimes A_{\lambda,\nu}$;
--   2. every block $A_{\lambda,\nu}$ of (294) is unitary.
--
--   The theorem removes every structural assumption of Remark 5.2 except the double-coset data; Theorem 5.4 is its multiplicity-free special case.
--
--   Differences from the source:
--   - encoding: orthonormal families of isometric embeddings $L^\omega_{\kappa,\nu,m}$, $E^\omega_{\lambda,\kappa,e}$ with orthogonal images spanning the target (290) → unitary block matrices whose columns are the embedded basis vectors, intertwining $\bigoplus_\kappa I\otimes R_\kappa$ with the target action, with arbitrary multiplicity counts; reason: the same data
--   - encoding: "the circuit in Figure 20 implements $U^\lambda_{\rm Ind}$" → $A_\lambda N_\lambda=U^\lambda_{\rm Ind}$ as matrices, $N_\lambda$ the product of the first three steps; reason: the formulation of the proof
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem C.2, p.87 (PDF p.88); §C.1–C.2 eqs. (284)–(294) and Figure 20 pp.84–86; Definition B.1 p.81

import Definitions.Def_GL2QFT_Supplement_MackeyMult

open Classical
open scoped Matrix

namespace GL2QFT

namespace Supplement

open Mackey MackeyMult

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem C.2 (Mackey induction with
multiplicities)**, p.87 (PDF p.88): "For every finite group `G`, subgroup `H ≤ G`, and `λ ∈ Ĥ`, the
circuit in Figure 20 implements `U^λ_Ind` in the bases fixed in Appendix C.1. Moreover, every block
`A_{λ,ν}` in Equation (294) is unitary."

Setting of Appendix C (pp.84–85): `Ω`, `H_ω`, `T_ω` and `T = ⊔ T_ω ω` as in Remark 5.2,
`n = [G:H]`, `n_ω = [H:H_ω]`; chosen representatives of the irreps of `H`, `G` and every `H_ω`; the
bases of the `G`-irreps subgroup-adapted to `H` with multiplicities (Definition B.1); no
multiplicity-freeness and no `H_ω`-adaptedness; any choice of the embeddings `L^ω_{κ,ν,m}` and
`E^ω_{λ,κ,e}` of (290). Then:
1. `A_λ N_λ = U^λ_Ind` (291), where `N_λ` is the first three steps of Figure 20 and
   `A_λ = ⊕_ν I ⊗ A_{λ,ν}` with the blocks (294);
2. every block `A_{λ,ν}` is unitary: `A A† = I` and `A† A = I`. -/
theorem theorem_C_2 {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsAdaptedMult H BH mult RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
    [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (mL : ∀ ω, ΛH → Λω ω → ℕ)
    (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
    (hL : ∀ ω ∈ Ω, ∀ ν, IsEmbeddingFamily H Bω (fun h => RH ν (h : H)) (mL ω ν) (Rω ω)
      (Lmat ω ν))
    (mE : ∀ ω, ΛH → Λω ω → ℕ)
    (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)
    (hE : ∀ ω ∈ Ω, ∀ l, IsEmbeddingFamily H Bω (twistRep H ω (RH l)) (mE ω l) (Rω ω) (Emat ω l))
    (l : ΛH) :
    AopM H Ω BH mult Bω RG mL Lmat mE Emat l * NopM H Ω Tω BH Bω RH mL Lmat mE Emat l =
        UIndMult H Ω Tω BH mult RG l ∧
      ∀ ν : ΛH,
        AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν *
            (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ = 1 ∧
          (AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν)ᴴ *
            AblockM H Ω BH mult Bω RG mL Lmat mE Emat l ν = 1 := by sorry

end Supplement

end GL2QFT
