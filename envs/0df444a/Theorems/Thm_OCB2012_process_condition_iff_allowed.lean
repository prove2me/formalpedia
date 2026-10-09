-- Prove2me | Theorems.Thm_OCB2012_process_condition_iff_allowed
-- name    : OCB2012.process_condition_iff_allowed
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-07T23:12:02.280625+00:00
-- url     : https://prove2.me/theorems/823d9101-861d-4fb3-8f40-a5319bb5db95
-- title:
--   Appendix C — characterization of condition (5) by Hilbert–Schmidt terms
-- statement:
--   Throughout, $A_1,A_2$ (Alice's input and output) and $B_1,B_2$ (Bob's) are finite-dimensional systems; operators on $A_1A_2B_1B_2$ are complex matrices in that tensor order. A CJ matrix $M^{X_1X_2}$ of a CPTP map satisfies $M\ge 0$ and $\operatorname{Tr}_{X_2}M=\mathbb 1^{X_1}$. For each system $X$ fix a Hilbert–Schmidt basis $\{\sigma^X_\mu\}_{\mu=0}^{d_X^2-1}$ with $\sigma^X_0=\mathbb 1$, $\sigma^X_j$ Hermitian and traceless for $j\ge1$, and $\operatorname{Tr}\sigma^X_\mu\sigma^X_\nu=d_X\delta_{\mu\nu}$. A term $\sigma^{A_1}_\mu\sigma^{A_2}_\nu\sigma^{B_1}_\lambda\sigma^{B_2}_\gamma$ is **allowed** if its set of non-identity factors is one of $\varnothing, A_1, B_1, A_1B_1, A_2B_1, A_1A_2B_1, A_1B_2, A_1B_1B_2$ (Fig. 3). Then for every Hermitian $W$ on $A_1A_2B_1B_2$:
--   $$\operatorname{Tr}[W(M^{A_1A_2}\otimes M^{B_1B_2})]=1\ \ \forall\,\text{CPTP CJ } M^{A_1A_2},M^{B_1B_2}$$
--   holds **if and only if** $\operatorname{Tr}W=d_{A_2}d_{B_2}$ and $\operatorname{Tr}[W\,\sigma^{A_1}_\mu\sigma^{A_2}_\nu\sigma^{B_1}_\lambda\sigma^{B_2}_\gamma]=0$ for every term that is not allowed, i.e. the Hilbert–Schmidt coefficients $w_{\mu\nu\lambda\gamma}$ of $W$ vanish outside the allowed types and $w_{0000}=1/(d_{A_1}d_{B_1})$.
--
--   **Formalization Note** The coefficient $w_{\mu\nu\lambda\gamma}$ equals $\operatorname{Tr}[W\sigma_\mu\sigma_\nu\sigma_\lambda\sigma_\gamma]/(d_{A_1}d_{A_2}d_{B_1}d_{B_2})$ by orthogonality, so vanishing coefficients are stated as vanishing traces. Hermiticity of $W$ and of the basis matches the source's restriction to real coefficients (Eq. (17)).
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix C, Eqs. (16)–(18) and the general form at the end of App. C; Fig. 3 (allowed terms), Fig. 4 (disallowed terms)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem process_condition_iff_allowed {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (BA1 : HSBasis a1) (BA2 : HSBasis a2) (BB1 : HSBasis b1) (BB2 : HSBasis b2)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : W.IsHermitian) :
    (∀ (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ),
        IsCPTP_CJ MA → IsCPTP_CJ MB → prob W MA MB = 1) ↔
      (W.trace = (Fintype.card a2 * Fintype.card b2 : ℂ) ∧
        ∀ μ ν l γ, ¬ AllowedType μ.isSome ν.isSome l.isSome γ.isSome →
          (W * ((BA1.σ μ ⊗ₖ BA2.σ ν) ⊗ₖ (BB1.σ l ⊗ₖ BB2.σ γ))).trace = 0) := by sorry

end OCB2012
