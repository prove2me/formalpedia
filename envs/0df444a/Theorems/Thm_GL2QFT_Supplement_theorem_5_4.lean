-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_5_4
-- name    : GL2QFT.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:42:41.924349+00:00
-- url     : https://prove2.me/theorems/df3bc207-0459-4eed-a8f6-54091bd20ea2
-- title:
--   Theorem 5.4 — the Mackey circuit implements $U^\lambda_{\rm Ind}$, and every $A_{\lambda,\tilde\lambda}$ is unitary
-- statement:
--   Assume Remark 5.2: $H\le G$ finite; $\Omega$ a double-coset transversal of $H\backslash G/H$; $H_\omega=H\cap\omega H\omega^{-1}$; $T_\omega$ a left transversal of $H_\omega$ in $H$ and $T=\bigsqcup_\omega T_\omega\omega$ (62); representatives of the irreps of $H$, $G$ and every $H_\omega$; the bases of the $G$-irreps subgroup-adapted to $H$, the fixed basis of every $\lambda\in\widehat H$ subgroup-adapted to every $H_\omega$ simultaneously; multiplicity-free decompositions of $\mathrm{Ind}^G_HV_\lambda$, $\mathrm{Ind}^H_{H_\omega}V_\kappa$ and the twisted modules $V^\omega_\lambda$; and any untwisting unitaries $U^\omega_{\rm twist}$ satisfying (67). Then for every $\lambda\in\widehat H$:
--   1. Algorithm 1 implements the induction transform:
--   $$A_\lambda N_\lambda=U^\lambda_{\rm Ind},$$
--   where $N_\lambda$ is Steps 1–3 (encoding, untwisting, smaller induction transforms) and $A_\lambda=\bigoplus_{\tilde\lambda}A_{\lambda,\tilde\lambda}\otimes I$ with the blocks (70);
--   2. every block $A_{\lambda,\tilde\lambda}:\mathbb C[K_{\lambda,\tilde\lambda}]\to\mathbb C[M_{\lambda,\tilde\lambda}]$ is unitary.
--
--   This reduces the induction transform to transforms for the smaller subgroups $H_\omega$ and the explicit blocks (70); it is the step used for $B<\mathrm{GL}_2(\mathbb F_q)$ in the proof of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: the multiplicity-freeness assumptions of Remark 5.2 → built into the label types (subgroup-adapted labels with predecessor sets; the codomain $\bigoplus_{\kappa\in N(\lambda^\omega)}V_\kappa$ of $U^\omega_{\rm twist}$); reason: for complete systems of irreps these are exactly the multiplicity-free decompositions
--   - encoding: one fixed basis of $\lambda$ adapted to every $H_\omega$ → one basis index type with, for each $\omega$, a relabelling onto the $H_\omega$-adapted labels satisfying (35); reason: the same basis, labelled per $\omega$
--   - encoding: "Algorithm 1 correctly implements $U^\lambda_{\rm Ind}$" → $A_\lambda N_\lambda=U^\lambda_{\rm Ind}$ as matrices, $N_\lambda$ the product of Steps 1–3; reason: the formulation of the proof, (71)
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 5.4, p.31 (PDF p.32); Remark 5.2 p.28, Definition 5.3 and Algorithm 1 pp.29–30

import Definitions.Def_GL2QFT_Supplement_Mackey

open Classical
open scoped Matrix

namespace GL2QFT

namespace Supplement

open Induction Mackey

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 5.4**, p.31 (PDF p.32): "Under the
assumptions of Remark 5.2, Algorithm 1, and equivalently the circuit in Figure 11, correctly
implements `U^λ_Ind`. Moreover, every `A_{λ,λ̃}` is unitary on the corresponding multiplicity space."

Assumptions of Remark 5.2 (p.28): `H ≤ G` finite; `Ω` a double-coset transversal for `H\G/H`;
`H_ω = H ∩ ωHω⁻¹`; `T_ω` a left transversal of `H_ω` in `H`; `T = ⊔_ω T_ω ω` (62); chosen
representatives `R_λ` (`λ ∈ Ĥ`), `R_μ` (`μ ∈ Ĝ`), `R_κ` (`κ ∈ Ĥ_ω`) of the irreps; the bases of the
`R_μ` subgroup-adapted to `H` (Gelfand–Tsetlin), the fixed basis of every `λ` subgroup-adapted to
every `H_ω` simultaneously; `U^ω_twist` any unitary satisfying (67). The multiplicity-freeness of
`Ind^G_H V_λ`, of `Ind^H_{H_ω} V_κ` and of `V^ω_λ` is built into the adapted labels and the codomain
of `U^ω_twist`. Then, for every `λ ∈ Ĥ`:
1. `A_λ N_λ = U^λ_Ind`, where `N_λ` is Steps 1–3 of Algorithm 1 and `A_λ = ⊕_λ̃ A_{λ,λ̃} ⊗ I` with
   the blocks (70);
2. every block `A_{λ,λ̃}` is unitary: `A A† = I` and `A† A = I`. -/
theorem theorem_5_4 {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G)
    (hΩ : IsDoubleCosetTransversal H H Ω) (Tω : G → Set H)
    (hTω : ∀ ω ∈ Ω, Subgroup.IsComplement (Tω ω) (interSub H ω : Set H))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
    [∀ ω κ, DecidableEq (Bω ω κ)]
    (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (hRω : ∀ ω ∈ Ω, IsIrrepSystem (Rω ω))
    (NmW : ∀ ω, ΛH → Finset (Λω ω)) (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)
    (hAdω : ∀ ω ∈ Ω, IsAdaptedToInter H BH RH Bω Rω NmW adapt ω)
    (Ntw : ∀ ω, ΛH → Finset (Λω ω)) (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)
    (hUtw : ∀ ω ∈ Ω, ∀ l, IsUntwisting H BH RH Bω Rω Ntw Utw ω l) (l : ΛH) :
    Aop H Ω BH Nminus RG Bω NmW adapt Ntw Utw l * Nop H Ω Tω BH RH Bω NmW adapt Ntw Utw l =
        UIndLam (mackeyT H Ω Tω) BH Nminus RG l ∧
      ∀ lt : ΛH,
        Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt *
            (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt)ᴴ = 1 ∧
          (Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt)ᴴ *
            Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l lt = 1 := by sorry

end Supplement

end GL2QFT
