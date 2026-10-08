-- Prove2me | Theorems.Thm_KonyaginUnitVectors_Alon_S_structure
-- name    : KonyaginUnitVectors.Alon.S_structure
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:15:32.284373+00:00
-- url     : https://prove2.me/theorems/5b56103a-300b-48a3-98fa-677fcf88e167
-- title:
--   Structure of the connection set S
-- statement:
--   Throughout, $F$ is a finite field of characteristic $2$ with $q$ elements, regarded as an algebra over $\mathbb F_2$ (for example $\mathrm{GF}(2^k)$), $\mathrm{Tr}:F\to\mathbb F_2$ is the absolute trace, and $\psi(y)=(-1)^{\mathrm{Tr}(y)}\in\{1,-1\}$ is the associated additive character of $F$.
--
--   Let $W_0,W_1$ be the two classes $\{x\ne0:\mathrm{Tr}(x^9)=0\}$, $\{x\ne0:\mathrm{Tr}(x^9)=1\}$, let $\gamma(x)=(x,x^3,x^5)$ and $S=\{\gamma(x)+\gamma(y):x\in W_0,\ y\in W_1\}\subseteq F^3$. Then:
--
--   1. the map $(x,y)\mapsto\gamma(x)+\gamma(y)$ is injective on $W_0\times W_1$;
--   2. $\gamma(x)+\gamma(y)\ne0$ for $x\in W_0$, $y\in W_1$ (in particular $0\notin S$);
--   3. no three elements $s_1,s_2,s_3\in S$ satisfy $s_1+s_2+s_3=0$;
--   4. $|S|=|W_0|\,|W_1|$;
--   5. $|W_0|+|W_1|+1=q$.
--
--   Property 3 says that the Cayley graph on $F^3$ with connection set $S$ is triangle-free, and properties 1 and 4 give the size of $S$; both are needed in Alon's construction of orthonormal labelings.
--
--   **Formalization Note.** `W0 F`, `W1 F`, `Sset F` and `gamma F` are the platform definitions of the definition module `KonyaginUnitVectors_AlonConstruction`.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction

namespace KonyaginUnitVectors.Alon

theorem S_structure (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] :
    Set.InjOn (fun p : F × F => gamma F p.1 + gamma F p.2) ↑(W0 F ×ˢ W1 F) ∧
    (∀ p ∈ W0 F ×ˢ W1 F, gamma F p.1 + gamma F p.2 ≠ 0) ∧
    (∀ s₁ ∈ Sset F, ∀ s₂ ∈ Sset F, ∀ s₃ ∈ Sset F, s₁ + s₂ + s₃ ≠ 0) ∧
    (Sset F).card = (W0 F).card * (W1 F).card ∧
    (W0 F).card + (W1 F).card + 1 = Fintype.card F := by sorry

end KonyaginUnitVectors.Alon
