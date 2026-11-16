-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_6_27
-- name    : GL2QFT.Supplement.theorem_6_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:15.627562+00:00
-- url     : https://prove2.me/theorems/3990511f-52cf-412c-9b3d-dfdb7937bcd9
-- title:
--   Theorem 6.27 — $R_{{\rm exc},\gamma}T_\gamma D_\gamma=A_\gamma$ on the source space ($q>2$)
-- statement:
--   Let $q>2$ (Remark 6.15) and $\gamma\in X_q$. Let $T_\gamma=R_{{\rm fix},\gamma}(\mathfrak F_\times\oplus\mathfrak F_{\ker N})B_\gamma\mathfrak F^\dagger_\times$ (158), with the gates of Definitions 6.16–6.21, for any choice of the unused labels of $R_{{\rm fix},\gamma}$ and any extension of the branch transforms. Then for every input state $|c\rangle\in\mathrm{span}\{|c_\infty\rangle,|c_\alpha\rangle:\alpha\in X_q\}$,
--   $$R_{{\rm exc},\gamma}\,T_\gamma\,D_\gamma\,(|c\rangle|0_{\rm work}\rangle)=(A_\gamma|c\rangle)\,|0_{\rm work}\rangle , \tag{166}$$
--   where $A_\gamma$ is the block (144)–(145).
--
--   This is the correctness of the circuit of Figure 14; together with the efficiency of each gate it gives Theorem 6.34.
--
--   **Formalization Note** The identity is stated as an equality of maps from the source register to $\mathbb C[\widehat G\sqcup\text{Unused}]$, on clean-work inputs. It was checked numerically for $q=3,5,7$ with random values on the free columns of the branch transform (`numerics/t627_check.py`).
--
--   Differences from the source:
--   - generalization: the antisymmetric combinations "sent to unused orthogonal labels" → any isometric $R_{{\rm fix},\gamma}$ satisfying (154)–(155) whose images of the antisymmetric combinations lie in the span of the unused labels; reason: covers every choice of unused labels
--   - generalization: the unitary extension of $\mathfrak F_\times\oplus\mathfrak F_{\ker N}$ to the register $\mathbb C^2\otimes\mathbb C[\mathbb F^*_{q^2}]$ → arbitrary values off $\mathrm{sp}\otimes\mathbb F^*_q$ and $\mathrm{ns}\otimes\ker N$; reason: covers every extension
--   - encoding: the work registers and the unitary extension of $B_\gamma$ → suppressed, with $B_\gamma$ the isometry (151)–(152); reason: on clean-work inputs every extension acts as $B_\gamma$, by its definition (p.49)
--   - encoding: (166) for every $|c\rangle$ in the span → equality of matrices on $\mathbb C[\{c_\infty\}\cup\{c_\alpha\}]$; reason: both sides are linear
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.27, eq. (166), p.52 (PDF p.53); Definitions 6.16–6.21 pp.49–50; Remark 6.15 p.48

import Definitions.Def_GL2QFT_Supplement_AGammaGates

open Classical

namespace GL2QFT

namespace Supplement

open FieldData AGammaGates

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 6.27**, p.52 (PDF p.53): "For every
input state `|c⟩ ∈ span{|c_∞⟩, |c_α⟩ : α ∈ X_q}`,
`R_exc,γ T_γ D_γ (|c⟩|0_work⟩) = (A_γ|c⟩)|0_work⟩` (166)", where `T_γ = R_fix,γ (F_× ⊕ F_{ker N}) B_γ F†_×`
(158).

For every field data `D` with `q > 2` (Remark 6.15: "for the remainder of this subsection we may
assume that `q > 2`"), every `γ ∈ X_q`, every set of unused labels, every admissible label-fixing gate
`R_fix,γ` (Definition 6.20) and every admissible branch transform `F_× ⊕ F_{ker N}` (Definition 6.19,
with any extension off `F*_q` and `ker N`):
`R_exc,γ R_fix,γ (F_× ⊕ F_{ker N}) B_γ F†_× D_γ = A_γ` as maps from the source register
`span{|c_∞⟩, |c_α⟩}` to `ℂ[Irr ⊕ Unused]`, with `A_γ` the published block (144)–(145).

**Formalization Note** All maps are written on clean-work inputs (the work registers in `|0⟩` are
suppressed), so the extensions of `B_γ` and of the branch transforms to the full register enter only
through their action on these inputs, which Definitions 6.18–6.19 prescribe. -/
theorem theorem_6_27 (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr) :
    Rexc D γ U * (Rfix * Mbr * Bgate D γ * FxDag D) * Dgate D γ = AGammaExt D γ U := by sorry

end Supplement

end GL2QFT
